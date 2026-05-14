from collections import deque
from dataclasses import asdict, dataclass
from fractions import Fraction
from types import SimpleNamespace as NS
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
from pyrsistent import PClass, PMap, PVector, field, m, v
import networkx as nx
import pygame as pg


def as_rgb(t: str) -> tuple[int, int, int]:
    as_hex = hashlib.md5(t.encode()).hexdigest()[:6]
    return tuple(int(as_hex[e : e + 2], 16) for e in (0, 2, 4))


Element = NS
Location = typing.NewType("Location", tuple[int, int, int])

SPELLS = {
    "mag ludm": lambda unit: unit.set("editor", not unit.editor),
    "hic": lambda unit: unit,
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

    offset: Location  # position relative to its anchor, (0, 0, 0) when it is the first

    delta: Location = (0, 0, 0)  # delta from another anchor

    enabled: bool = False
    id: int = 0  # incremental integer ID

    def __getattr__(self, name: str):
        if name == "x":
            return self.offset[0]

        if name == "y":
            return self.offset[1]

        if name == "z":
            return self.offset[2]

        raise AttributeError(name)

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

        data["offset"] = data["delta"]

        if data["id"] == 1:
            data["offset"] = (0, 0, 0)

        self.table.append(Anchor(**data))

    def get(self, id: int) -> Anchor:
        return self.table[id - 1]


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

    anchor_id: int = 0  # anchor ID

    state: typing.Literal["idle"] = "idle"
    targetted: bool = False
    choice: tuple[int, int] = (0, 0)

    @classmethod
    def fromdict(cls, data: dict):
        return Tile(**dict(data, sprites=Sprites.fromdict(data["sprites"])))

    def relative(self, startpoint: Location, change: Location) -> Location:
        return tuple(a - b + c for a, b, c in zip(startpoint, change, self.delta))

    def sprite(self):
        x, y = self.choice
        cut: tuple[int, int, int, int] = x * 32, y * 32, 32, 32

        image = sources[self.sprites.mode[self.state].key]

        if self.targetted:
            new = image.copy()
            new.fill((50, 50, 50, 0), special_flags=pg.BLEND_RGBA_ADD)
            image = new

        return image, cut


class Unit(PClass):

    name: str = field(str)
    health: int = field(int)
    stamina: int = field(int)

    sprites: Sprites = field(type=Sprites)

    progress: Fraction = field(type=Fraction, initial=Fraction(1, 1))
    action: tuple[int, int, int] = field(type=tuple, initial=(100, 100, 150))

    anchor_id: int = field(factory=lambda v: v or 0)  # anchor ID

    state: typing.Literal["idle", "run", "cast", "block", "dance"] = field(
        type=str, initial="idle"
    )

    client: bool = field(type=bool, initial=False)
    editor: bool = field(type=bool, initial=False)
    targetted: bool = field(type=bool, initial=False)
    stepped: int = field(type=int, initial=0)

    delta: Location = field(type=tuple, initial=(100, 100, 0))
    o: typing.Literal["S", "E", "W", "N"] = field(type=str, initial="N")

    color: typing.Literal["red", "green", "yellow", "blue"] = field(
        type=str, initial="yellow"
    )

    @classmethod
    def fromdict(cls, data: dict):
        return Unit(**dict(data, sprites=Sprites.fromdict(data["sprites"])))

    def relative(self, startpoint: Location, change: Location) -> Location:
        return tuple(a - b + c for a, b, c in zip(startpoint, change, self.delta))

    def sprite(self):
        _ = ["S", "E", "W", "N"]

        x = 0
        y = _.index(self.o) * 32

        active = self.sprites.mode[self.state]
        image = sources[active.key]

        x = next(cycles[active.key])

        if self.targetted:
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
    def resources(unit: Unit) -> list[Element]:
        bar_w, bar_h = (100, 2)

        max_hp = unit.stamina * 3

        anchor = anchors.get(unit.anchor_id)
        _x, _y, _z = unit.delta

        if not anchor.within(unit.delta):
            return []

        ratio = math.floor(unit.health * 100 / max_hp)
        stats = pg.font.SysFont(None, 14).render(
            f"{unit.health}/{unit.stamina*3}", True, (255, 255, 255)
        )
        state = pg.font.SysFont(None, 14).render(
            f"{unit.name}: Game master" if (unit.editor) else unit.name,
            True,
            (255, 255, 255),
        )

        progress = []

        if unit.progress < 1:
            progress = [
                Element(
                    type="RECT",
                    rect=pg.Rect(unit.delta[0] - 100, unit.delta[1] - 100, 100, 3),
                    color=(30, 30, 30),
                    z=anchor.z + _z,
                ),
                Element(
                    type="RECT",
                    rect=pg.Rect(
                        unit.delta[0] - 101,
                        unit.delta[1] - 101,
                        round(unit.progress * 100),
                        3,
                    ),
                    color=unit.action,
                    z=anchor.z + _z,
                ),
            ]

        return progress + [
            Element(
                type="RECT",
                rect=pg.Rect(
                    anchor.x + _x - 30, anchor.y + _y - 30, bar_w / 100 * 32, bar_h
                ),
                color=(0, 0, 0),
                z=anchor.z + _z,
            ),
            Element(
                type="RECT",
                rect=pg.Rect(
                    anchor.x + _x - 30 + 2,
                    anchor.y + _y - 30 + 2,
                    ratio / 100 * 32,
                    bar_h,
                ),
                color=(0, 255, 0) if ratio > 50 else (255, 0, 0),
                z=anchor.z + _z,
            ),
            Element(
                type="IMAGE",
                obj=stats,
                rect=(anchor.x + _x - 50, anchor.y + _y - 50, 32, 32),
                z=anchor.z + _z,
            ),
            Element(
                type="IMAGE",
                obj=state,
                rect=(anchor.x + _x - 70, anchor.y + _y - 70, 32, 32),
                z=anchor.z + _z,
            ),
        ]

    @staticmethod
    def tile(player: Unit, tile: Tile) -> list[Element]:
        sprite, cut = tile.sprite()

        obj = pg.Surface([32, 32], pg.SRCALPHA)

        obj.blit(sprite, (0, 0), cut)
        obj.set_colorkey("black")

        if tile.targetted:
            obj.fill((30, 30, 30, 0), special_flags=pg.BLEND_RGBA_ADD)

        _x, _y, _z = tile.delta

        visible = []

        anchor = anchors.get(tile.anchor_id)
        if not anchor.within(tile.delta):
            return []

        return [
            Element(
                type="IMAGE",
                obj=obj,
                rect=(anchor.x + _x, anchor.y + _y, 32, 32),
                z=anchor.z + _z,
            )
        ]

    @staticmethod
    def unit(unit: Unit) -> list[Element]:
        obj = pg.Surface([32, 32]).convert()

        sprite, cut = unit.sprite()

        obj.blit(sprite, (0, 0), cut)
        obj.set_colorkey("black")

        _x, _y, _z = unit.delta

        visible = []

        anchor = anchors.get(unit.anchor_id)
        if not anchor.within(unit.delta):
            return []

        if unit.targetted:
            visible.append(
                Element(
                    type="ELLIPSE",
                    color=unit.color,
                    rect=(anchor.x + _x, anchor.y + _y, 32, 32 / 2),
                    z=anchor.z + _z,
                    width=2,
                )
            )

        visible.append(
            Element(
                type="IMAGE",
                obj=obj,
                rect=(anchor.x + _x - 32, anchor.y + _y - 32, 32, 32),
                z=anchor.z + _z,
            )
        )

        return visible


class Game(PClass):
    option: typing.Iterator = field()

    splash: bool = field()
    events: deque = field()
    running: bool = field()

    tiles: list[Tile] = field()
    others: dict[str, [Unit]] = field()  # easier to keep a separate list
    units: list[Unit] = field()
    controlled: list[int] = field()  # index of unit

    targets: typing.Iterable[int] = field(initial=iter([]))
    targetted = field(type=(int, type(None)))

    choice = field(initial=(0, 0))
    night = field(type=bool, initial=True)

    def elements(self) -> list[Element]:
        # col, row, width, height

        project = functools.partial(projected, virtual.width, virtual.height)
        player = self.units[self.controlled[0]]

        return [
            *map(
                project,
                itertools.chain(
                    *map(functools.partial(Render.tile, player), self.tiles)
                ),
            ),
            *map(
                project,
                itertools.chain(
                    *map(Render.unit, itertools.chain(self.units, self.others.values()))
                ),
            ),
            *map(
                project,
                itertools.chain(
                    *map(
                        Render.resources,
                        itertools.chain(self.units, self.others.values()),
                    )
                ),
            ),
        ]

    def controls(
        self, unit: Unit, game: "Game", keys: dict[int, bool], mx: int, my: int
    ) -> tuple[Unit, "Game"]:
        if keys[pg.K_TAB]:
            # cycle targets
            pass

        return unit, game

    def anchoring(self, unit: Unit) -> Unit | None:
        candidate = self.facing(unit)
        if candidate is None:
            return None

        _, ref_id, edge = candidate
        pos = unit.relative((0, 0, 0), edge["delta"])
        new = anchors.get(ref_id)

        if new.within(pos):
            return unit.set("anchor_id", new.id).set("delta", pos)

    def accessible(self, unit: Unit, relevant: list[Location]) -> bool:
        return self.position(*unit.delta) in relevant

    def facing(self, unit: Unit) -> tuple[int, int, dict]:
        """which anchor is the unit facing

        ...
        """

        old = anchors.get(unit.anchor_id)
        candidate = min(
            filter(
                lambda e: (
                    ((unit.delta[0] < 0) == ((e[2]["delta"][0] - old.delta[0]) < 0))
                    and ((unit.delta[1] < 0) == ((e[2]["delta"][1] - old.delta[1]) < 0))
                    and ((unit.delta[2] < 0) == ((e[2]["delta"][2] - old.delta[2]) < 0))
                ),
                world.edges(unit.anchor_id, data=True),
            ),
            key=lambda e: abs(e[2]["weight"]),
            default=None,
        )

        if candidate is None:
            return None

        return candidate

    def movements(
        self, unit: Unit, keys: dict[int, bool], mx: int, my: int
    ) -> Unit | None:
        if not any([keys[k] for k in [pg.K_w, pg.K_s, pg.K_a, pg.K_d]]):
            return unit.set("state", "idle").set("stepped", 0)

        distance = unit.distance()
        runner: Unit = unit.set("state", "run").set(
            "stepped", unit.stepped + 1 if unit.stepped < 100 else 6
        )

        if keys[pg.K_w]:
            return runner.set("o", "N").set(
                "delta", (unit.delta[0], unit.delta[1] - distance, unit.delta[2])
            )

        if keys[pg.K_s]:
            return runner.set("o", "S").set(
                "delta", (unit.delta[0], unit.delta[1] + distance, unit.delta[2])
            )

        if keys[pg.K_a]:
            return runner.set("o", "W").set(
                "delta", (unit.delta[0] - distance, unit.delta[1], unit.delta[2])
            )

        if keys[pg.K_d]:
            return runner.set("o", "E").set(
                "delta", (unit.delta[0] + distance, unit.delta[1], unit.delta[2])
            )

        return None

    def control(self, keys: dict[int, bool], mx: int, my: int):
        player = self.units[self.controlled[0]]
        _x, _y, _z = player.delta

        for u_idx in self.controlled:
            unit = self.units[u_idx]
            x, y, z = unit.delta

            if not any([keys[pg.K_w], keys[pg.K_s], keys[pg.K_a], keys[pg.K_d]]):

                unit.state = "idle"
                unit.stepped = 0
                step = 0
            else:
                # camera.x, camera.y = iso(-1 * _x, -1 * _y)
                step = unit.step()

            if keys[pg.K_w]:
                position = self.at_tile(x, y - step, z)
                if -1 < position:
                    # unit.z = self.accessible[position][-1]
                    unit.o = "N"
                    unit.delta = (x, y - step, z)

            if keys[pg.K_s]:
                position = self.at_tile(x, y + step, z)
                if -1 < position:
                    unit.o = "S"
                    unit.delta = (x, y + step, z)

            if keys[pg.K_a]:
                position = self.at_tile(x - step, y, z)
                if -1 < position:
                    unit.o = "W"
                    unit.delta = (x - step, y, z)

            if keys[pg.K_d]:
                position = self.at_tile(x + step, y, z)
                if -1 < position:
                    unit.o = "E"
                    unit.delta = (x + step, y, z)

        if keys[pg.K_TAB]:
            if not player.editor:
                self.targetted = next(self.targets)
                for e in self.units:
                    e.targetted = False

                self.units[self.targetted].targetted = True

            if player.editor:
                player = self.units[self.controlled[0]]
                nearby = lambda e: e.delta[0] in range(_x - 16, _x + 16) and e.delta[
                    1
                ] in range(_y - 16, _y + 16)

                target = next(filter(nearby, self.tiles), None)

                if target is not None:
                    for e in self.tiles:
                        e.targetted = e == target

        if player.editor and (
            keys[pg.K_f] or keys[pg.K_r] or keys[pg.K_y] or keys[pg.K_h] or keys[pg.K_x]
        ):
            target = next(filter(operator.attrgetter("targetted"), self.tiles), None)
            if target is not None:
                if keys[pg.K_f]:
                    target.choice = next(self.option)
                    self.choice = target.choice

                if keys[pg.K_r]:
                    target.choice = self.choice

                if keys[pg.K_y]:
                    target.z += 1
                    if target.z > 100:
                        target.z = -100

                if keys[pg.K_h]:
                    target.z -= 1
                    if target.z < -100:
                        target.z = 100

                if keys[pg.K_x]:
                    target.z = 0

        if player.editor and keys[pg.K_g]:
            params = [-1]

            r = rebase = lambda v: 32 * (v // 32)

            match player.o:
                case "S":
                    params = r(_x), r(_y) + 32, r(_z)
                case "E":
                    params = r(_x) + 32, r(_y), r(_z)
                case "W":
                    params = r(_x) - 32, r(_y), r(_z)
                case "N":
                    params = r(_x), r(_y) - 32, r(_z)

            if keys[pg.K_g] and self.at_tile(*params) < 0:
                self.tiles.append(
                    Tile(
                        params,
                        choice=self.choice,
                        sprites=models["ground"],
                        anchor_id=player.anchor_id,
                    )
                )

                self.tiles = sorted(self.tiles, key=lambda e: e.delta)

        if player.editor and keys[pg.K_t]:
            self.units.append(
                Unit(
                    delta=(_x, _y, _z),
                    health=20,
                    stamina=10,
                    sprites=random.choice(
                        [models["wolf"], models["boar"], models["stag"]]
                    ),
                    targetted=False,
                    o="S",
                    anchor_id=player.anchor_id,
                )
            )

            self.targets = itertools.cycle(range(0, len(self.units)))

        if player.editor and (keys[pg.K_s] and keys[pg.K_LCTRL]):
            universe = json.dumps(
                list(map(asdict, self.tiles)) + list(map(asdict, self.units))
            )
            self.running = False

            with open("universe.json", "w") as f:
                f.write(universe)

            time.sleep(1)
            self.running = True

        if keys[pg.K_SPACE]:
            camera.x, camera.y = iso(-1 * _x, -1 * _y)

        if not pg.mouse.get_focused():
            return

        padding = screen.width // 12

        if mx <= padding:
            camera.x += 10

        if mx >= screen.width - padding:
            camera.x -= 10

        if my <= padding:
            camera.y += 10

        if my >= screen.height - padding:
            camera.y -= 10

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
                    ]
                ),
                ("localhost", 8818),
            )

            while True:
                data, server = sock.recvfrom(1024)
                if not data:
                    return

                anchor_id, player, delta, o, state, health, stamina = pickle.loads(data)
                self.others[player] = Unit(
                    name=player,
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

    def act(
        self, act: list[str], target: Unit, game: "Game"
    ) -> tuple[list[str], Unit, "Game"]:
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

                    if current is None:
                        if not opener:
                            act.clear()

                    target = target.set(
                        "progress", Fraction(len(concept), len(current))
                    ).set("action", as_rgb(current))

                    if concept == current:
                        act.clear()
                        target = ACTIONS[concept](target)

                if ev.type == pg.MOUSEMOTION:
                    pass

            time.sleep(0.01)

        return act, target, game


if __name__ == "__main__":

    started_at = pg.time.get_ticks()
    pg.init()

    pg.mixer.init()

    pg.mixer.music.load("lost in the meadows_0.flac")
    pg.mixer.music.play(-1)
    pg.mixer.music.set_volume(0.2)

    sound_step = [
        pg.mixer.Sound("Fantozzi-StoneL1.ogg"),
        pg.mixer.Sound("Fantozzi-StoneR1.ogg"),
    ]

    foot = itertools.cycle([0, 1])

    sound_step[0].set_volume(0.01)
    sound_step[1].set_volume(0.01)

    screen = pg.display.set_mode((900, 600), pg.RESIZABLE)
    pg.display.set_caption("r/untitledMMORPG")

    anchors = Anchors.create()

    anchors.add(
        dict(
            radius=32,
            delta=(0, 0, 0),
            enabled=True,
        )
    )

    anchors.add(
        dict(
            radius=32,
            delta=(32 * 6, 0, 0),
            enabled=True,
        )
    )

    anchors.add(
        dict(
            radius=32,
            delta=(-32, 32 * 10, 0),
            enabled=True,
        )
    )

    world = nx.DiGraph()

    delta = (255, 0, 0)
    world.add_edge(
        1,
        2,
        delta=anchors.get(2).delta,
        weight=math.dist((0, 0, 0), anchors.get(2).delta),
    )

    world.add_edge(
        2,
        1,
        delta=tuple(-1 * e for e in anchors.get(2).delta),
        weight=math.dist((0, 0, 0), (-1 * e for e in anchors.get(2).delta)),
    )

    world.add_edge(
        1,
        3,
        delta=anchors.get(3).delta,
        weight=math.dist((0, 0, 0), anchors.get(3).delta),
    )

    world.add_edge(
        3,
        1,
        delta=tuple(-1 * e for e in anchors.get(3).delta),
        weight=math.dist((0, 0, 0), (-1 * e for e in anchors.get(3).delta)),
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
        units = []
        for e in json.loads(f.read()):
            if "client" in e:
                units.append(Unit.fromdict(e))
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
        splash=True,
        events=deque([]),
        running=True,
        tiles=tiles,
        units=units,
        others={},
        targets=itertools.cycle(range(0, len(units))),
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
            )

        if sys.argv[1] == "c":
            p1 = Unit(
                name="wolf",
                sprites=models["wolf"],
                client=True,
                delta=(0, 0, 0),
                health=80,
                stamina=50,
                color="blue",
                anchor_id=2,
            )

        g.units.append(p1)

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

    g = (
        g.set("units", sorted(g.units, key=operator.attrgetter("client")))
        .set("controlled", [len(g.units) - 1])
        .set("running", True)
    )

    clock = pg.time.Clock()

    # state = threading.Thread(target=g.loop, daemon=True)
    # state.start()

    virtual = pg.Surface((640, 480))
    act = []

    while g.running:
        for ev in pg.event.get():
            if pg.QUIT == ev.type:
                g.running = False

            if pg.VIDEORESIZE == ev.type:
                screen = pg.display.set_mode((ev.w, ev.h), pg.RESIZABLE)

            g.events.append(ev)

        if not g.running:
            pg.quit()
            break

        for u_idx, unit in enumerate(g.units):
            if u_idx not in g.controlled:
                continue

            initial: Unit = unit

            moved: Unit = (
                g.movements(unit, pg.key.get_pressed(), *pg.mouse.get_pos()) or initial
            )

            if moved != initial:
                if moved.stepped % 4 == 0:
                    sound_step[next(foot)].play()
                g.units[u_idx] = moved

            anchored: Unit = g.anchoring(moved) or moved

            if anchored != moved:
                g.units[u_idx] = anchored

            relevant = lambda to, e: e.anchor_id == to

            is_relevant = functools.partial(relevant, anchored.anchor_id)

            legal: bool = g.accessible(
                anchored,
                map(
                    operator.attrgetter("delta"),
                    filter(is_relevant, g.tiles),
                ),
            )

            candidate = g.facing(anchored)
            if candidate is not None:
                one, other, edge = candidate

                is_relevant = functools.partial(relevant, other)

                possible = g.accessible(
                    anchored.set("delta", anchored.relative((0, 0, 0), edge["delta"])),
                    map(operator.attrgetter("delta"), filter(is_relevant, g.tiles)),
                )

                legal = legal or possible

            if not legal:
                g.units[u_idx] = initial

            act, acted, g = g.act(act, anchored, g)
            if acted != anchored:
                g.units[u_idx] = acted

            controlled, g = g.controls(
                unit, g, pg.key.get_pressed(), *pg.mouse.get_pos()
            )

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

    state.join()
    pg.quit()
