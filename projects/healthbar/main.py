from collections import deque
from dataclasses import (
    asdict,
    dataclass,
    field as datafield,
    fields as datafields,
    replace,
)
from fractions import Fraction
from types import SimpleNamespace as NS
from uuid import uuid4
import functools
import itertools
import json
import hashlib
import math
import operator
import os
import pickle
import random
import socket
import sys
import threading
import time
import typing


from matplotlib import pyplot
from pyrsistent import PClass, PMap, PVector, field, m, ny, v
import networkx as nx
import pygame as pg


def as_rgb(t: str) -> tuple[int, int, int]:
    as_hex = hashlib.md5(t.encode()).hexdigest()[:6]
    return tuple(int(as_hex[e : e + 2], 16) for e in (0, 2, 4))


Element = NS
Location = typing.NewType("Location", tuple[int, int, int])


editor_gate = lambda cb: cb()


def friendo(unit, game):
    new = game.make_unit(unit)
    return (
        unit,
        (game if not unit.editor else game.set("units", game.units.set(new.guid, new))),
    )


def modo(unit, game):
    choice = next(game.option)

    return (
        unit,
        (
            game
            if not unit.editor
            else game.set("choice", choice).set(
                "tiles",
                list(
                    map(
                        lambda e: (replace(e, choice=choice) if e.targeted else e),
                        game.tiles,
                    )
                ),
            )
        ),
    )


SPELLS = {
    "gemumasuta": lambda unit, game: (unit.set("editor", not unit.editor), game),
    "hic": lambda unit, game: (unit, game),
    "kiku": lambda unit, game: (
        unit,
        (
            game
            if not unit.editor
            else game.set(
                "tiles",
                sorted(game.tiles + game.make_tile(unit), key=lambda e: e.delta),
            )
        ),
    ),
    "saibai": modo,
    "henshin": lambda unit, game: (
        unit,
        (
            game
            if not unit.editor
            else game.set(
                "tiles",
                list(
                    map(
                        lambda e: replace(e, choice=game.choice) if e.targeted else e,
                        game.tiles,
                    )
                ),
            )
        ),
    ),
    "torinozoku": lambda unit, game: (
        unit,
        (
            game
            if not unit.editor
            else game.set(
                "tiles",
                list(
                    filter(
                        lambda e: not e.targeted
                        or (
                            game.position(*unit.delta) == e.delta
                            if unit.anchor_id == e.anchor_id
                            else True
                        ),
                        game.tiles,
                    )
                ),
            )
        ),
    ),
    "yujin": friendo,
    "masuku": lambda unit, game: (
        unit,
        (
            game
            if not unit.editor
            else game.set(
                "units",
                game.units.transform(
                    (next(k for k in game.units if game.units[k].targeted), "sprites"),
                    models[next(game.model)],
                ),
            )
        ),
    ),
    "kieru": lambda unit, game: (
        unit,
        (
            game
            if not unit.editor
            else game.set(
                "units",
                game.units.discard(
                    next(k for k in game.units if game.units[k].targeted)
                ),
            )
        ),
    ),
    "ugoku": lambda unit, game: (
        (
            unit
            if not unit.editor
            else unit.set(
                "effects",
                unit.effects.append(
                    Effect(
                        tags=v(*["game-master"]),
                        name="mover",
                        started_at=game.ticks // 1000,
                        duration=30,
                    )
                ),
            )
        ),
        game,
    ),  # move targeted thing
}

CRAFTS = {}

ACTIONS = SPELLS | CRAFTS


def iso(x: int, y: int) -> tuple[int, int]:
    return ((x - y) * 0.5, ((x + y) // 2) * 0.5)


def projected(width, height, element: Element) -> Element:
    x, y, _w, _h = element.rect

    horizontal = width // 2
    vertical = 100 - element.z  # (height // 2) - element.z

    _x, _y = iso(x, y)

    x, y = (camera.x + horizontal + _x, camera.y + vertical + _y)
    element.rect = x, y, _w, _h
    return element


@dataclass
class Anchor:
    radius: int  # number of pixels in each direction

    guid: str = datafield(default_factory=lambda: str(uuid4()))

    targeted: bool = False
    enabled: bool = False
    id: int = 0  # incremental integer ID

    def within(self, location: Location) -> bool:
        diameter = range(-1 * (self.radius * 2), 1 + (self.radius * 2))

        for e in location:
            if e not in diameter:
                return False

        return True


@dataclass
class Anchors:
    """manager class for anchor objects, it mimicks a DB storage"""

    table: list[Anchor]  # Anchor.id must be equivalent to index+1

    @classmethod
    def create(cls):
        return Anchors(table=[])

    def add(self, data: dict) -> Anchor:
        data["id"] = len(self.table) + 1
        self.table.append(Anchor(**data))

    def get(self, id: int) -> Anchor:
        return self.table[id - 1]


class Effect(PClass):
    tags: PVector[str] = field()
    name: str = field()
    started_at: int = field()
    duration: int = field()  # in seconds
    value: int = field(initial=0)


@dataclass
class Sprite:
    key: str

    # following are mods in order to make the sprite
    # positioning work in a 32x32 system
    x: int = 0
    y: int = 0
    w: int = 0
    h: int = 0


@dataclass
class Sprites:
    mode: dict[str, Sprite]

    @classmethod
    def fromdict(cls, data: dict):
        return Sprites(mode={k: Sprite(**data["mode"][k]) for k in data["mode"]})


@dataclass
class Tile:

    delta: Location
    sprites: Sprites

    guid: str = datafield(default_factory=lambda: str(uuid4()))
    anchor_id: int = 0  # anchor ID

    state: typing.Literal["idle"] = "idle"
    targeted: bool = False
    choice: tuple[int, int] = (0, 0)

    @classmethod
    def fromdict(cls, data: dict):
        return Tile(
            **dict(
                data,
                delta=tuple(data["delta"]),
                sprites=Sprites.fromdict(data["sprites"]),
            )
        )

    def relative(self, to: Location) -> Location:
        return tuple(a - b for a, b in zip(self.delta, to))

    def sprite(self):
        x, y = self.choice
        cut: tuple[int, int, int, int] = x * 32, y * 32, 32, 32

        image = sources[self.sprites.mode[self.state].key]

        if self.targeted:
            new = image.copy()
            new.fill((50, 50, 50, 0), special_flags=pg.BLEND_RGBA_ADD)
            image = new

        return image, cut


class Unit(PClass):

    name: str = field(str)
    health: int = field(int)
    stamina: int = field(int)

    effects: PVector[Effect] = field(initial=v())
    sprites: Sprites = field(type=Sprites)

    guid = field(type=str, initial=lambda: str(uuid4()))
    progress: Fraction = field(type=Fraction, initial=Fraction(1, 1))
    action: tuple[int, int, int] = field(type=tuple, initial=(100, 100, 150))

    anchor_id: int = field(factory=lambda v: v or 0)  # anchor ID
    overlaps: list[int] = field(factory=lambda v: v or [])

    state: typing.Literal["idle", "run", "cast", "block", "dance"] = field(
        type=str, initial="idle"
    )

    client: bool = field(type=bool, initial=False)
    editor: bool = field(type=bool, initial=False)
    targeted: bool = field(type=bool, initial=False)
    stepped: int = field(type=int, initial=0)

    delta: Location = field(type=tuple, initial=(100, 100, 0))
    o: typing.Literal["S", "E", "W", "N"] = field(type=str, initial="N")

    color: typing.Literal["red", "green", "yellow", "blue"] = field(
        type=str, initial="yellow"
    )

    @classmethod
    def fromdict(cls, data: dict):
        return Unit(
            **dict(
                data,
                effects=v(*data.get("effects", [])),
                sprites=Sprites.fromdict(data["sprites"]),
            )
        )

    def relative(self, to: Location) -> Location:
        return tuple(a - b for a, b in zip(self.delta, to))

    def sprite(self):
        _ = ["S", "E", "W", "N"]

        x = 0
        y = _.index(self.o) * 32

        active = self.sprites.mode[self.state]
        image = sources[active.key]

        if tock:
            frame[active.key] = next(cycles[active.key])

        x = frame[active.key]

        if self.targeted:
            new = image.copy()
            new.fill((50, 50, 50, 0), special_flags=pg.BLEND_RGBA_ADD)
            image = new

        return image, (x + active.x, y + active.y, 32 + active.w, 32 + active.h)

    def distance(self) -> int:
        if self.stepped > 10:
            return 5

        return 3


class Render:
    """turns game elements into renderable pygame objects"""

    @staticmethod
    def resources(player: Unit, unit: Unit) -> list[Element]:
        bar_w, bar_h = (100, 2)

        max_hp = unit.stamina * 3

        anchor = anchors.get(unit.anchor_id)

        if not anchor.within(unit.delta):
            return []

        edge = {"delta": (0, 0, 0)}

        if world.has_edge(player.anchor_id, unit.anchor_id):
            edge = world.get_edge_data(player.anchor_id, unit.anchor_id)

        ratio = math.floor(unit.health * 100 / max_hp)
        stats = pg.font.SysFont(None, 14).render(
            f"{unit.health}/{unit.stamina*3}", True, (255, 255, 255)
        )

        effects = unit.effects

        title = unit.name
        if unit.effects:
            for e in unit.effects:
                title += " " + e.name

        state = pg.font.SysFont(None, 14).render(
            (f"{title}: Game master" if (unit.editor) else title),
            True,
            (255, 255, 255),
        )

        progress = []

        if unit.progress < 1:
            progress = [
                Element(
                    type="RECT",
                    rect=pg.Rect(
                        edge["delta"][0] + unit.delta[0] - 100,
                        edge["delta"][1] + unit.delta[1] - 100,
                        100,
                        3,
                    ),
                    color=(30, 30, 30),
                    z=edge["delta"][2] + unit.delta[2],
                ),
                Element(
                    type="RECT",
                    rect=pg.Rect(
                        edge["delta"][0] + unit.delta[0] - 101,
                        edge["delta"][1] + unit.delta[1] - 101,
                        round(unit.progress * 100),
                        3,
                    ),
                    color=unit.action,
                    z=edge["delta"][2] + unit.delta[2],
                ),
            ]

        return progress + [
            Element(
                type="RECT",
                rect=pg.Rect(
                    edge["delta"][0] + unit.delta[0] - 30,
                    edge["delta"][1] + unit.delta[1] - 30,
                    bar_w / 100 * 32,
                    bar_h,
                ),
                color=(0, 0, 0),
                z=edge["delta"][2] + unit.delta[2],
            ),
            Element(
                type="RECT",
                rect=pg.Rect(
                    edge["delta"][0] + unit.delta[0] - 30 + 2,
                    edge["delta"][1] + unit.delta[1] - 30 + 2,
                    ratio / 100 * 32,
                    bar_h,
                ),
                color=(0, 255, 0) if ratio > 50 else (255, 0, 0),
                z=edge["delta"][2] + unit.delta[2],
            ),
            Element(
                type="IMAGE",
                obj=stats,
                rect=(
                    edge["delta"][0] + unit.delta[0] - 50,
                    edge["delta"][1] + unit.delta[1] - 50,
                    32,
                    32,
                ),
                z=edge["delta"][2] + unit.delta[2],
            ),
            Element(
                type="IMAGE",
                obj=state,
                rect=(
                    edge["delta"][0] + unit.delta[0] - 70,
                    edge["delta"][1] + unit.delta[1] - 70,
                    32,
                    32,
                ),
                z=edge["delta"][2] + unit.delta[2],
            ),
        ]

    @staticmethod
    def tile(player: Unit, tile: Tile) -> list[Element]:
        sprite, cut = tile.sprite()

        obj = pg.Surface([32, 32], pg.SRCALPHA)

        obj.blit(sprite, (0, 0), cut)
        obj.set_colorkey("black")

        if tile.targeted:
            obj.fill((30, 30, 30, 0), special_flags=pg.BLEND_RGBA_ADD)

        visible = []

        anchor = anchors.get(tile.anchor_id)
        if not anchor.within(tile.delta):
            return []

        edge = {"delta": (0, 0, 0)}

        if world.has_edge(player.anchor_id, tile.anchor_id):
            edge = world.get_edge_data(player.anchor_id, tile.anchor_id)

        return [
            Element(
                type="IMAGE",
                obj=obj,
                rect=(
                    edge["delta"][0] + tile.delta[0],
                    edge["delta"][1] + tile.delta[1],
                    32,
                    32,
                ),
                z=edge["delta"][2] + tile.delta[2],
            )
        ]

    @staticmethod
    def unit(player: Unit, unit: Unit) -> list[Element]:
        obj = pg.Surface([32, 32]).convert()

        sprite, cut = unit.sprite()

        obj.blit(sprite, (0, 0), cut)
        obj.set_colorkey("black")

        visible = []

        anchor = anchors.get(unit.anchor_id)
        if not anchor.within(unit.delta):
            return []

        edge = {"delta": (0, 0, 0)}
        if world.has_edge(player.anchor_id, unit.anchor_id):
            edge = world.get_edge_data(player.anchor_id, unit.anchor_id)

        if unit.targeted:
            visible.append(
                Element(
                    type="ELLIPSE",
                    color=unit.color,
                    rect=(
                        edge["delta"][0] + unit.delta[0],
                        edge["delta"][1] + unit.delta[1],
                        32,
                        32 / 2,
                    ),
                    z=edge["delta"][2] + unit.delta[2],
                    width=2,
                )
            )

        visible.append(
            Element(
                type="IMAGE",
                obj=obj,
                rect=(
                    edge["delta"][0] + unit.delta[0] - 32,
                    edge["delta"][1] + unit.delta[1] - 32,
                    32,
                    32,
                ),
                z=edge["delta"][2] + unit.delta[2],
            )
        )

        return visible

    @staticmethod
    def anchor(player: Unit, anchor: Anchor) -> list[Element]:
        edge = {"delta": (0, 0, 0)}

        if world.has_edge(player.anchor_id, anchor.id):
            edge = world.get_edge_data(player.anchor_id, anchor.id)

        return [
            Element(
                type="ELLIPSE",
                color="pink",
                rect=(edge["delta"][0], edge["delta"][1], 32, 32 / 2),
                z=edge["delta"][2],
                width=2,
            )
        ]


class Game(PClass):
    option: typing.Iterator = field()
    model = field()

    ticks: int = field()
    splash: bool = field()
    events: deque = field()
    running: bool = field()

    tiles: list[Tile] = field()
    others: dict[str, [Unit]] = field()  # easier to keep a separate list
    units: PMap[str, PVector[Unit]] = field(type=PMap)
    controlled: list[int] = field()  # index of unit

    cycle = field()  # the cycle
    targets = field()  # the tuple of targets

    choice = field(initial=(0, 0))
    character = field(type=str)
    night = field(type=bool, initial=True)

    def elements(self) -> list[Element]:
        # col, row, width, height

        project = functools.partial(projected, virtual.width, virtual.height)
        player = self.units[self.controlled[0]]

        return [
            *map(
                project,
                itertools.chain(
                    *map(
                        functools.partial(Render.tile, player),
                        sorted(self.tiles, key=lambda e: e.delta),
                    )
                ),
            ),
            *map(
                project,
                itertools.chain(
                    *map(
                        functools.partial(Render.unit, player),
                        itertools.chain(self.units.values(), self.others.values()),
                    )
                ),
            ),
            *map(
                project,
                itertools.chain(
                    *map(
                        functools.partial(Render.resources, player),
                        itertools.chain(self.units.values(), self.others.values()),
                    )
                ),
            ),
            *map(
                project,
                itertools.chain(
                    *map(
                        functools.partial(Render.anchor, player),
                        filter(lambda e: e.targeted, anchors.table),
                    )
                ),
            ),
        ]

    def controls(self, keys: dict[int, bool], mx: int, my: int, clicks: dict) -> "Game":
        if keys[pg.K_TAB]:
            target = next(self.cycle)

            for a_idx, anchor in enumerate(anchors.table):
                anchors.table[a_idx].targeted = anchor.guid == target

            return (
                self.set(
                    "tiles",
                    list(
                        map(lambda e: replace(e, targeted=e.guid == target), self.tiles)
                    ),
                )
                .set(
                    "units",
                    self.units.transform(
                        [ny], lambda e: e.set("targeted", e.guid == target)
                    ),
                )
                .set(
                    "others",
                    {
                        k: v.set("targeted", v.guid == target)
                        for k, v in self.others.items()
                    },
                )
            )

        if keys[pg.K_s] and keys[pg.K_LCTRL]:
            with open("universe.json", "w+") as f:
                f.write(json.dumps(list(map(asdict, self.tiles))))
                time.sleep(3)

        if not pg.mouse.get_focused():
            return self

        if not self.running:
            return self

        padding = screen.width // 12

        if mx <= padding:
            camera.x += 10

        if mx >= screen.width - padding:
            camera.x -= 10

        if my <= padding:
            camera.y += 10

        if my >= screen.height - padding:
            camera.y -= 10

        if clicks[2]:
            camera.x, camera.y = iso(
                -1 * self.units[self.controlled[0]].delta[0],
                -1 * self.units[self.controlled[0]].delta[1],
            )

        return self

    def anchoring(self) -> "Game":
        unit: Unit = self.units[self.controlled[0]]

        candidate = self.facing(unit)
        if candidate is None:
            return self

        _, ref_id, edge = candidate
        pos = unit.relative(edge["delta"])
        new = anchors.get(ref_id)
        old = anchors.get(unit.anchor_id)

        if old.within(unit.delta):
            return self.transform(
                ("units", unit.guid), lambda e: e.set("overlaps", e.overlaps if new.id in e.overlaps else e.overlaps + [new.id])
            )

        if not new.within(pos):
            return self.transform(
                ("units", unit.guid),
                lambda e: e.set(
                    "overlaps",
                    list(filter(functools.partial(operator.ne, new.id), e.overlaps)),
                ),
            )

        return self.transform(
            ("units", unit.guid),
            lambda e: e.set("anchor_id", new.id).set("delta", pos),
        )

    def accessible(self, location: Location, relevant: list[Location]) -> bool:
        return self.position(*location) in relevant

    def facing(self, unit: Unit) -> tuple[int, int, dict]:
        """which anchor is the unit facing

        ...
        """

        old = anchors.get(unit.anchor_id)
        candidate = min(
            filter(
                lambda e: (
                    ((unit.delta[0] < 0) == ((e[2]["delta"][0]) < 0))
                    and ((unit.delta[1] < 0) == ((e[2]["delta"][1]) < 0))
                    and ((unit.delta[2] < 0) == ((e[2]["delta"][2]) < 0))
                ),
                world.edges(unit.anchor_id, data=True),
            ),
            key=lambda e: abs(e[2]["weight"]),
            default=None,
        )

        if candidate is None:
            return None

        return candidate

    def movements(self, keys: dict[int, bool], mx: int, my: int) -> "Game":
        target: Anchor | Unit | None = self.units[self.controlled[0]]

        if unit.editor and any(filter(lambda e: e.name == "mover", unit.effects)):
            target = next(filter(operator.attrgetter("targeted"), anchors.table), None)

            if target is None:
                target = next(
                    filter(operator.attrgetter("targeted"), self.units.values()), None
                )

        if isinstance(target, Unit):
            if not any([keys[k] for k in [pg.K_w, pg.K_s, pg.K_a, pg.K_d]]):
                return self.transform(
                    ("units", target.guid),
                    lambda e: e.set("state", "idle").set("stepped", 0),
                )

            distance = target.distance()
            runner: Unit = target.set("state", "run").set(
                "stepped", target.stepped + 1 if target.stepped < 100 else 6
            )

            if keys[pg.K_w]:
                runner = runner.set("o", "N").set(
                    "delta",
                    (target.delta[0], target.delta[1] - distance, target.delta[2]),
                )

            if keys[pg.K_s]:
                runner = runner.set("o", "S").set(
                    "delta",
                    (target.delta[0], target.delta[1] + distance, target.delta[2]),
                )

            if keys[pg.K_a]:
                runner = runner.set("o", "W").set(
                    "delta",
                    (target.delta[0] - distance, target.delta[1], target.delta[2]),
                )

            if keys[pg.K_d]:
                runner = runner.set("o", "E").set(
                    "delta",
                    (target.delta[0] + distance, target.delta[1], target.delta[2]),
                )

            return self.transform(("units", runner.guid), lambda e: runner)

        if (
            isinstance(target, Anchor)
            and target.id != self.units[self.controlled[0]].anchor_id
        ):
            if not any([keys[k] for k in [pg.K_w, pg.K_s, pg.K_a, pg.K_d]]):
                return self

            idx = anchors.table.index(target)
            u, v, data = min(
                list(world.edges(target.id, data=True)),
                key=lambda e: abs(e[2]["weight"]),
            )
            x, y, z = data["delta"]

            old = new = data["delta"]

            if keys[pg.K_w]:
                new = (x, y + 32, z)
            if keys[pg.K_s]:
                new = (x, y - 32, z)
            if keys[pg.K_a]:
                new = (x + 32, y, z)
            if keys[pg.K_d]:
                new = (x - 32, y, z)

            a = data.copy()
            a["delta"] = new
            a["weight"] = math.dist((0, 0, 0), a["delta"])

            b = data.copy()
            b["delta"] = tuple(-1 * e for e in new)
            b["weight"] = math.dist((0, 0, 0), b["delta"])

            world.add_edge(u, v, **a)
            world.add_edge(v, u, **b)

            for e in world.edges(v, data=True):
                u1, v1, secondary = e
                if u1 != v:
                    continue

                if u == v1:
                    continue

                one, other = (u, v1)
                relation = v

                first, second = (
                    world[one][relation]["delta"],
                    world[other][relation]["delta"],
                )

                delta = tuple(a - b for a, b in zip(first, second))
                weight = math.dist((0, 0, 0), delta)
                world.add_edge(one, other, weight=weight, delta=delta)

                delta = tuple(-1 * e for e in delta)
                weight = math.dist((0, 0, 0), delta)
                world.add_edge(other, one, weight=weight, delta=delta)

                return self

        return self

    def effects(self) -> "Game":
        unit: Unit = self.units[self.controlled[0]]
        game = self

        for e_idx, e in enumerate(unit.effects):
            if "game-master" in e.tags:
                if e.started_at + e.duration < self.ticks // 1000:
                    game = self.transform(
                        ("units", unit.guid),
                        lambda e: e.set("effects", unit.effects.delete(e_idx)),
                    )

        return game

    def notify(self, unit: PMap) -> None:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
            sock.sendto(
                pickle.dumps(
                    [
                        unit.anchor_id,
                        unit.name,
                        unit.delta,
                        unit.o,
                        unit.state,
                        unit.health,
                        unit.stamina,
                        unit.guid,
                    ]
                ),
                ("localhost", 8818),
            )

            while True:
                data, server = sock.recvfrom(1024)
                if not data:
                    return

                anchor_id, player, delta, o, state, health, stamina, guid = (
                    pickle.loads(data)
                )
                self.others[guid] = Unit(
                    name=player,
                    guid=guid,
                    health=health,
                    stamina=stamina,
                    o=o,
                    state=state,
                    sprites=models[player],
                    delta=delta,
                    anchor_id=anchor_id,
                )

    def position(self, x: int, y: int, z: int):
        _x = 32 * (x // 32)
        _y = 32 * (y // 32)
        _z = 8 * (z // 8)

        return (_x, _y, _z)

    def act(self, act: list[str]) -> tuple[list[str], "Game"]:
        game = self
        target = next(
            filter(operator.attrgetter("targeted"), self.units.values()), None
        )
        target = target or self.units[self.controlled[0]]

        while self.events:
            ev = self.events.popleft()
            if ev is not None:
                if ev.type == pg.KEYDOWN:
                    # hotkeys/actions
                    opener = ev.unicode == "/"

                    if opener:
                        act = []

                    act.append(ev.unicode)

                    if len(act) > 50:
                        act.pop(0)

                    concept = "".join(act[1:]).lower()
                    current = next(
                        filter(lambda e: concept and e.startswith(concept), ACTIONS),
                        "/",
                    )

                    if current == "/":
                        if not opener:
                            act.clear()

                    target = target.set(
                        "progress", Fraction(len(concept) or 1, len(current))
                    ).set("action", as_rgb(current))

                    if concept == current:
                        act.clear()
                        target, game = ACTIONS[concept](target, game)

                if ev.type == pg.MOUSEMOTION:
                    pass

            time.sleep(0.01)

        return act, game.transform(("units", target.guid), lambda e: target)

    def make_tile(self, unit: Unit) -> list[Tile]:
        params = [-1]

        r = rebase = lambda v: 32 * (v // 32)
        _x, _y, _z = unit.delta

        match unit.o:
            case "S":
                params = r(_x), r(_y) + 32, r(_z)
            case "E":
                params = r(_x) + 32, r(_y), r(_z)
            case "W":
                params = r(_x) - 32, r(_y), r(_z)
            case "N":
                params = r(_x), r(_y) - 32, r(_z)

        if any(e for e in self.tiles if e.delta == params):
            return []

        return [
            Tile(
                params,
                choice=self.choice,
                sprites=models["ground"],
                anchor_id=unit.anchor_id,
            )
        ]

    def make_unit(self, unit: Unit) -> Unit:
        return Unit(
            name="wolpe",
            delta=unit.delta,
            health=20,
            stamina=10,
            sprites=models[self.character],
            targeted=False,
            o="S",
            anchor_id=unit.anchor_id,
        )


if __name__ == "__main__":

    started_at = pg.time.get_ticks()
    pg.init()

    pg.mixer.init()

    pg.mixer.music.load("lost in the meadows_0.flac")
    pg.mixer.music.play(-1)
    pg.mixer.music.set_volume(1)

    sound_step = [
        pg.mixer.Sound("Fantozzi-StoneL1.ogg"),
        pg.mixer.Sound("Fantozzi-StoneR1.ogg"),
    ]

    foot = itertools.cycle([0, 1])

    sound_step[0].set_volume(0.1)
    sound_step[1].set_volume(0.1)

    screen = pg.display.set_mode((900, 600), pg.RESIZABLE)
    pg.display.set_caption("r/untitledMMORPG")

    anchors = Anchors.create()

    anchors.add(
        dict(
            radius=32,
            enabled=True,
        )
    )

    anchors.add(
        dict(
            radius=32,
            enabled=True,
        )
    )

    anchors.add(
        dict(
            radius=32,
            enabled=True,
        )
    )

    world = nx.DiGraph()
    world.add_edge(
        1,
        2,
        delta=(7 * 32, 0, 0),
        weight=math.dist((0, 0, 0), (7 * 32, 0, 0)),
    )

    world.add_edge(
        2,
        1,
        delta=(-7 * 32, 0, 0),
        weight=math.dist((0, 0, 0), (-7 * 32, 0, 0)),
    )

    world.add_edge(
        1,
        3,
        delta=(-32, 10 * 32, 0),
        weight=math.dist((0, 0, 0), (-32, 10 * 32, 0)),
    )

    world.add_edge(
        3,
        1,
        delta=(32, -10 * 32, 0),
        weight=math.dist((0, 0, 0), (32, -10 * 32, 0)),
    )

    if False:
        pos = nx.spring_layout(world)

        nx.draw(world, pos, with_labels=True)
        nx.draw_networkx_edge_labels(
            world, pos, edge_labels=nx.get_edge_attributes(world, "delta")
        )

        pyplot.show()
        sys.exit(0)

    camera = NS(x=0, y=0)

    cycles: dict[str, typing.Iterable] = {"ground_idle": itertools.cycle([])}
    frame: dict[str, typing.Any] = {}

    sources: dict[str, pg.image] = {
        "ground_idle": pg.image.load("spritesheet.png").convert_alpha()
    }

    models = {
        "ground": Sprites(
            mode={
                "idle": Sprite(
                    key="ground_idle",
                )
            }
        ),
    }

    def sprite_model(
        model: str, dimensions: tuple[int, int], sheets: list[str, typing.Callable]
    ) -> Sprites:
        modes = {}
        sprite_width, sprite_height = dimensions

        for mode, sheet in sheets:
            raw = sheet()
            img = pg.transform.scale(
                raw, (raw.width * 32 / sprite_width, raw.height * 32 / sprite_height)
            )

            key = f"{model}_{mode}"
            cycles[key] = itertools.cycle(range(0, img.width, 32))
            sources[key] = img.convert_alpha()
            frame[key] = 0

            modes[mode] = Sprite(key=key)

        return Sprites(mode=modes)

    def sprite_stitch(height: int, width: int, path: str) -> pg.Surface:
        orientations = ["SW", "SE", "NW", "NE"]
        directions = len(orientations)
        surface = pg.Surface((width, height * directions), pg.SRCALPHA)

        for o_idx, o in enumerate(orientations):
            tmp = pg.image.load(path.format(orientation=o)).convert_alpha()
            surface.blit(tmp, (0, o_idx * height))

        return surface

    for model, dimensions, sheets in [
        (
            "wolf",
            (64, 64),
            [
                ("run", functools.partial(pg.image.load, "critters/wolf/wolf-run.png")),
                (
                    "idle",
                    functools.partial(pg.image.load, "critters/wolf/wolf-idle.png"),
                ),
            ],
        ),
        (
            "boar",
            (41, 30),
            [
                (
                    "run",
                    functools.partial(
                        sprite_stitch,
                        30,
                        164,
                        "critters/boar/boar_{orientation}_run_strip.png",
                    ),
                ),
                (
                    "idle",
                    functools.partial(
                        sprite_stitch,
                        30,
                        287,
                        "critters/boar/boar_{orientation}_idle_strip.png",
                    ),
                ),
            ],
        ),
        (
            "stag",
            (32, 41),
            [
                (
                    "run",
                    functools.partial(
                        sprite_stitch,
                        41,
                        320,
                        "critters/stag/critter_stag_{orientation}_run.png",
                    ),
                ),
                (
                    "idle",
                    functools.partial(
                        sprite_stitch,
                        41,
                        768,
                        "critters/stag/critter_stag_{orientation}_idle.png",
                    ),
                ),
            ],
        ),
    ]:
        models[model] = sprite_model(model, dimensions, sheets)

    with open("universe.json", "r") as f:
        tiles = []
        units = m()
        for e in json.loads(f.read()):
            if "client" in e:
                units = units.set(e["guid"], Unit.fromdict(e))
                continue

            tiles.append(Tile.fromdict(e))

    g = Game(
        option=itertools.cycle(
            list(
                sorted(
                    itertools.product(range(0, 11), range(0, 11)),
                    key=lambda e: e[1],
                )
            )
        ),
        model=itertools.cycle(["stag", "boar", "wolf"]),
        ticks=pg.time.get_ticks(),
        splash=True,
        events=deque([]),
        running=True,
        targets=tuple(),
        tiles=tiles,
        character="stag",
        units=units,
        others={},
        controlled=[],
    )

    if not g.units:
        p1 = Unit(
            name="stag",
            sprites=models["stag"],
            client=True,
            delta=(0, 0, 0),
            o="N",
            state="idle",
            health=90,
            stamina=50,
            color="blue",
            anchor_id=1,
            overlaps=[],
        )

        if sys.argv[1] == "b":
            p1 = Unit(
                name="boar",
                sprites=models["boar"],
                client=True,
                delta=(32, 0, 0),
                health=40,
                stamina=50,
                color="blue",
                anchor_id=1,
                overlaps=[],
            )

        npc1 = Unit(
            name="wolf",
            sprites=models["wolf"],
            client=False,
            delta=(0, 0, 0),
            health=80,
            stamina=50,
            color="blue",
            anchor_id=2,
            overlaps=[],
        )

        g = g.set("units", g.units.set(p1.guid, p1).set(npc1.guid, npc1))

    if not g.tiles:
        t1 = Tile(delta=(0, 0, 0), sprites=models["ground"], anchor_id=1)
        t2 = Tile(delta=(32, 0, 0), sprites=models["ground"], anchor_id=1)
        t3 = Tile(delta=(64, 0, 0), sprites=models["ground"], anchor_id=1)
        t4 = Tile(delta=(96, 0, 0), sprites=models["ground"], anchor_id=1)

        t5 = Tile(delta=(128, 0, 0), sprites=models["ground"], anchor_id=1)

        t6 = Tile(delta=(-64, 0, 0), sprites=models["ground"], anchor_id=2)
        t7 = Tile(delta=(-32, 0, 0), sprites=models["ground"], anchor_id=2)
        t8 = Tile(delta=(0, 0, 0), sprites=models["ground"], anchor_id=2)
        t9 = Tile(delta=(0, 32, 0), sprites=models["ground"], anchor_id=2)
        t10 = Tile(delta=(0, 64, 0), sprites=models["ground"], anchor_id=2)

        t11 = Tile(delta=(0, 0, 0), sprites=models["ground"], anchor_id=3)

        if not g.tiles:
            g.tiles.append(t1)
            g.tiles.append(t2)
            g.tiles.append(t3)
            g.tiles.append(t4)

            g.tiles.append(t5)

            g.tiles.append(t6)
            g.tiles.append(t7)
            g.tiles.append(t8)
            g.tiles.append(t9)
            g.tiles.append(t10)

            g.tiles.append(t11)

    g = g.set("units", g.units).set("controlled", [p1.guid]).set("running", True)

    clock = pg.time.Clock()

    # state = threading.Thread(target=g.loop, daemon=True)
    # state.start()

    virtual = pg.Surface((640, 480))
    act = []

    last = pg.time.get_ticks()
    while g.running:
        tock = False
        now = pg.time.get_ticks()

        if now - last >= 200:
            tock = True
            last = now

        for ev in pg.event.get():
            if pg.QUIT == ev.type:
                g = g.set("running", False)

            if pg.VIDEORESIZE == ev.type:
                screen = pg.display.set_mode((ev.w, ev.h), pg.RESIZABLE)

            g.events.append(ev)

        if not g.running:
            pg.quit()
            break

        g = g.set("ticks", now)

        for guid, unit in g.units.items():
            if guid not in g.controlled:
                continue

            initial: Unit = unit

            g = g.movements(pg.key.get_pressed(), *pg.mouse.get_pos())

            if tock:  # g.units[guid].stepped % 5 == 0:
                pass  # sound_step[next(foot)].play()

            g = g.anchoring()

            relevant = lambda presence, e: e.anchor_id in presence
            is_relevant = functools.partial(
                relevant, [g.units[guid].anchor_id]
            )

            legal: bool = g.accessible(
                g.units[guid].delta,
                map(
                    operator.attrgetter("delta"),
                    filter(is_relevant, g.tiles),
                ),
            )

            candidate = g.facing(g.units[guid])
            if candidate is not None:
                one, other, edge = candidate

                is_relevant = functools.partial(relevant, [other])

                possible = g.accessible(
                    g.units[guid].relative(edge["delta"]),
                    map(operator.attrgetter("delta"), filter(is_relevant, g.tiles)),
                )
                legal = legal or possible

            if not legal:
                g = g.set("units", g.units.set(guid, initial))

            act, g = g.act(act)

            tile = []
            if g.units[guid].editor:
                tile = [
                    e
                    for e in g.tiles
                    if e.anchor_id == g.units[guid].anchor_id
                    and g.accessible(g.units[guid].delta, [e.delta])
                ]

            targets = tuple(
                set(
                    map(
                        operator.attrgetter("guid"),
                        itertools.chain(
                            tile, g.units.values(), g.others.values(), anchors.table
                        ),
                    )
                )
            )

            if g.targets != targets:
                g = g.set("targets", targets).set("cycle", itertools.cycle(targets))

            g = g.controls(
                pg.key.get_pressed(), *pg.mouse.get_pos(), pg.mouse.get_pressed()
            )
            g = g.effects()

        if pg.time.get_ticks() % 2000:
            g.notify(g.units[g.controlled[0]])

        virtual.fill("black") if g.night else virtual.fill((135, 206, 235))

        if g.splash:
            if pg.time.get_ticks() - started_at > 1000:
                g = g.set("splash", False)

        if g.splash:
            screen.blit(
                pg.font.SysFont("monospace", 14).render(
                    "Loading...", False, (255, 255, 255)
                ),
                (100, 100),
            )
            pg.display.flip()
            continue

        for e in g.elements():
            if e.type == "IMAGE":
                virtual.blit(e.obj, e.rect)

            if e.type == "RECT":
                pg.draw.rect(virtual, e.color, e.rect)

            if e.type == "ELLIPSE":
                pg.draw.ellipse(virtual, e.color, e.rect, e.width)

        scaled = pg.transform.scale(virtual, (screen.width, screen.height))

        screen.blit(scaled, (0, 0))

        pg.display.flip()
        clock.tick(10)

    # state.join()
    pg.quit()
