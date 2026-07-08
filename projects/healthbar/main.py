# /// script
# dependencies = [
#   "pygame-ce",
#   "cffi",
#   "networkx",
#   "pillow",
#   "pyrsistent"
# ]
# ///

from collections import deque
from contextlib import suppress
from dataclasses import (
    asdict,
    dataclass,
    field as datafield,
    fields as datafields,
    replace,
)
from datetime import datetime
from fractions import Fraction
from os.path import dirname, exists, join
from pathlib import Path
from types import SimpleNamespace as NS
from uuid import uuid4
import asyncio
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


# from matplotlib import pyplot
from PIL import Image
from pyrsistent import PClass, PMap, PVector, field, m, ny, v as vec
import networkx as nx
import pygame as pg


def as_rgb(t: str) -> tuple[int, int, int]:
    as_hex = hashlib.md5(t.encode()).hexdigest()[:6]
    return tuple(int(as_hex[e : e + 2], 16) for e in (0, 2, 4))


SCALE = 32


def from_px(v: int) -> int:
    return v // SCALE


def to_px(v: int) -> int:
    return v * SCALE


Element = NS
Location = typing.NewType("Location", tuple[int, int, int])


editor_gate = lambda cb: cb()


def yujin(unit, game):
    new = game.make_unit(unit)
    return (
        unit,
        (game if not unit.editor else game.set("units", game.units.set(new.guid, new))),
    )


def masuku(unit, game):
    model = next(game.model)
    target = next(k for k in game.units if game.units[k].targeted)

    return (
        unit,
        (
            game
            if not unit.editor
            else game.set(
                "units",
                game.units.transform(
                    (
                        target,
                        "sprites",
                    ),
                    models[model],
                ),
            )
        ),
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
                vec(
                    *map(
                        lambda e: (replace(e, choice=choice) if e.targeted else e),
                        game.tiles,
                    )
                ),
            )
        ),
    )


def kiku(unit, game):
    if not unit.editor:
        return unit, game

    created = game.make_tile(unit)

    if not created:
        return unit, game

    game = game.set(
        "tiles", vec(*sorted(game.tiles.append(created), key=lambda e: e.delta))
    )

    return unit, game


def tochi(unit, game):
    if not unit.editor:
        return unit, game

    created = game.make_anchor(unit)

    if not created:
        return unit, game

    game = game.set(
        "anchors",
        game.anchors
        + vec(
            created,
        ),
    ).set(
        "tiles",
        vec(
            *sorted(
                game.tiles.append(
                    Tile(
                        (0, 0, 0),
                        choice=COLORMAP.tile[(128, 64, 0)],
                        sprites=models["ground"],
                        anchor_id=created.id,
                    )
                ),
                key=lambda e: e.delta,
            )
        ),
    )

    return unit, game


SPELLS = {
    "gemumasuta": lambda unit, game: (unit.set("editor", not unit.editor), game),
    "hic": lambda unit, game: (unit, game),
    "kiku": kiku,
    "tochi": tochi,
    "saibai": modo,
    "henshin": lambda unit, game: (
        unit,
        (
            game
            if not unit.editor
            else game.set(
                "tiles",
                vec(
                    *map(
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
                vec(
                    *filter(
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
    "yujin": yujin,
    "masuku": masuku,
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
                        tags=vec(*["game-master"]),
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


async def main():

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

        centerpoint: tuple[int, int] = (0, 0)
        dimensions: tuple[int, int] = (1, 1)
        guid: str = datafield(default_factory=lambda: str(uuid4()))

        targeted: bool = False
        enabled: bool = False
        id: int = 0  # incremental integer ID

        def within(self, location: Location) -> bool:
            x, y, z = location
            xc, yc = self.centerpoint

            diameter = self.radius * 2

            dist = SCALE * 3 + self.dimensions[0] // 2
            if x not in range(xc - dist, xc + dist):
                return False

            dist = SCALE * 3 + self.dimensions[1] // 2
            if y not in range(yc - dist, yc + dist):
                return False

            return True

        def recentered(self, relevant: typing.Iterator[object]) -> "Anchor":
            i1, i2, i3, i4 = itertools.tee(relevant, 4)

            t, l, b, r = (
                min(map(lambda e: e.delta[1], i1)),
                min(map(lambda e: e.delta[0], i2)),
                max(map(lambda e: e.delta[1], i3)),
                max(map(lambda e: e.delta[0], i4)),
            )

            width = r - l
            height = b - t

            x = l + (width // 2)
            y = t + (height // 2)

            self.centerpoint = (x, y)
            self.dimensions = (width, height)
            return self

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
        choice: tuple[int, int] = (1, 1)

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
            cut: tuple[int, int, int, int] = 32 * (x - 1), 32 * (y - 1), 32, 32

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

        effects: PVector[Effect] = field(initial=vec())
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
        jumped: int = field(type=int, initial=0)

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
                    effects=vec(*data.get("effects", [])),
                    sprites=Sprites.fromdict(data["sprites"]),
                )
            )

        def relative(self, to: Location) -> Location:
            return tuple(a - b for a, b in zip(self.delta, to))

        def sprite(self):
            _ = ["S", "E", "W", "N"]

            x = 0
            y = 32 * _.index(self.o)

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
                return 6

            return 4

    class Render:
        """turns game elements into renderable pygame objects"""

        @staticmethod
        def resources(game: "Game", player: Unit, unit: Unit) -> list[Element]:
            bar_w, bar_h = (100, 2)

            max_hp = unit.stamina * 3

            anchor = game.get_anchor(unit.anchor_id)

            if not anchor.within(unit.delta):
                return []

            edge = {"delta": (0, 0, 0)}

            if game.world.has_edge(unit.anchor_id, player.anchor_id):
                edge = game.world.get_edge_data(unit.anchor_id, player.anchor_id)

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
                        to_px(bar_w / 100),
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
                        to_px(ratio / 100),
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
                        SCALE,
                        SCALE,
                    ),
                    z=edge["delta"][2] + unit.delta[2],
                ),
                Element(
                    type="IMAGE",
                    obj=state,
                    rect=(
                        edge["delta"][0] + unit.delta[0] - 70,
                        edge["delta"][1] + unit.delta[1] - 70,
                        SCALE,
                        SCALE,
                    ),
                    z=edge["delta"][2] + unit.delta[2],
                ),
            ]

        @staticmethod
        def tile(game: "Game", player: Unit, tile: Tile) -> list[Element]:
            sprite, cut = tile.sprite()

            obj = pg.Surface([SCALE, SCALE], pg.SRCALPHA)

            obj.blit(sprite, (0, 0), cut)
            obj.set_colorkey("black")
            obj.set_alpha(50)

            if tile.targeted:
                obj.fill((30, 30, 30, 0), special_flags=pg.BLEND_RGBA_ADD)

            visible = []

            anchor = game.get_anchor(tile.anchor_id)
            if anchor.within(tile.delta):
                obj.set_alpha(255)

            edge = {"delta": (0, 0, 0)}

            if game.world.has_edge(tile.anchor_id, player.anchor_id):
                edge = game.world.get_edge_data(tile.anchor_id, player.anchor_id)

            return [
                Element(
                    type="IMAGE",
                    obj=obj,
                    rect=(
                        edge["delta"][0] + tile.delta[0],
                        edge["delta"][1] + tile.delta[1],
                        SCALE,
                        SCALE,
                    ),
                    z=edge["delta"][2] + tile.delta[2],
                )
            ]

        @staticmethod
        def unit(game: "Game", player: Unit, unit: Unit) -> list[Element]:
            obj = pg.Surface([SCALE, SCALE]).convert()

            sprite, cut = unit.sprite()

            obj.blit(sprite, (0, 0), cut)
            obj.set_colorkey("black")
            obj.set_alpha(50)

            visible = []

            anchor = game.get_anchor(unit.anchor_id)
            if anchor.within(unit.delta):
                obj.set_alpha(255)

            edge = {"delta": (0, 0, 0)}
            if game.world.has_edge(unit.anchor_id, player.anchor_id):
                edge = game.world.get_edge_data(unit.anchor_id, player.anchor_id)

            if unit.targeted:
                visible.append(
                    Element(
                        type="ELLIPSE",
                        color=unit.color,
                        rect=(
                            edge["delta"][0] + unit.delta[0],
                            edge["delta"][1] + unit.delta[1],
                            SCALE,
                            SCALE / 2,
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
                        edge["delta"][0] + unit.delta[0] - SCALE,
                        edge["delta"][1] + unit.delta[1] - SCALE,
                        SCALE,
                        SCALE,
                    ),
                    z=edge["delta"][2] + unit.delta[2],
                )
            )

            return visible

        @staticmethod
        def anchor(game: "Game", player: Unit, anchor: Anchor) -> list[Element]:
            edge = {"delta": (0, 0, 0)}

            if game.world.has_edge(anchor.id, player.anchor_id):
                edge = game.world.get_edge_data(anchor.id, player.anchor_id)

            return [
                Element(
                    type="ELLIPSE",
                    color="pink",
                    rect=(edge["delta"][0], edge["delta"][1], SCALE, SCALE / 2),
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

        anchors: PVector[Anchor] = field()
        tiles: PVector[Tile] = field()
        others: dict[str, [Unit]] = field()  # easier to keep a separate list
        units: PMap[str, Unit] = field(type=PMap)
        world: nx.DiGraph = field()

        controlled: list[int] = field()  # index of unit

        cycle = field()  # the cycle
        targets = field()  # the tuple of targets

        choice = field(initial=(1, 1))
        character = field(type=str)
        night = field(type=bool, initial=True)

        def elements(self, screen: object) -> list[Element]:
            # col, row, width, height

            project = functools.partial(projected, screen.width, screen.height)
            player = self.units[self.controlled[0]]

            def distance(e) -> tuple[int, int, int]:
                truedist = e.relative(
                    self.world[player.anchor_id][e.anchor_id]["delta"]
                    if self.world.has_edge(player.anchor_id, e.anchor_id)
                    else (0, 0, 0)
                )

                return (truedist[1], truedist[0], truedist[2])

            return [
                *map(
                    project,
                    itertools.chain(
                        *map(
                            functools.partial(Render.tile, self, player),
                            sorted(self.tiles, key=distance),
                        )
                    ),
                ),
                *map(
                    project,
                    itertools.chain(
                        *map(
                            functools.partial(Render.unit, self, player),
                            itertools.chain(self.units.values(), self.others.values()),
                        )
                    ),
                ),
                *map(
                    project,
                    itertools.chain(
                        *map(
                            functools.partial(Render.resources, self, player),
                            itertools.chain(self.units.values(), self.others.values()),
                        )
                    ),
                ),
                *map(
                    project,
                    itertools.chain(
                        *map(
                            functools.partial(Render.anchor, self, player),
                            filter(lambda e: e.targeted, self.anchors),
                        )
                    ),
                ),
            ]

        def controls(
            self, keys: dict[int, bool], mx: int, my: int, clicks: dict, screen: object
        ) -> "Game":
            if keys[pg.K_TAB]:
                target = next(self.cycle)

                for a_idx, anchor in enumerate(self.anchors):
                    self.anchors[a_idx].targeted = anchor.guid == target

                return (
                    self.set(
                        "tiles",
                        vec(
                            *map(
                                lambda e: replace(e, targeted=e.guid == target),
                                self.tiles,
                            )
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

            if (
                self.units[self.controlled[0]].editor
                and keys[pg.K_s]
                and keys[pg.K_LCTRL]
            ):
                anchors = {}
                images = {}
                sizes = {}

                for e in self.anchors:
                    Path(join("world", str(e.id))).mkdir(exist_ok=True)
                    relevant = filter(lambda t: t.anchor_id == e.id, self.tiles)
                    i1, i2, i3 = itertools.tee(relevant, 3)

                    reference = e.recentered(i1)

                    size = tuple(map(from_px, reference.dimensions))
                    size_of_image = tuple(
                        map(functools.partial(operator.add, 1), size),
                    )

                    offset = (
                        from_px(min(map(lambda e: e.delta[0], i2))),
                        from_px(min(map(lambda e: e.delta[1], i3))),
                    )

                    path = join("world", str(e.id), "tilemap.png")
                    sizes[path] = size_of_image

                    if path not in images:
                        assert reference.dimensions != (0, 0)
                        images[path] = Image.new("RGBA", size_of_image)

                    for t in self.tiles:
                        if t.anchor_id != e.id:
                            continue

                        color = COLORMAP_R.tile.get(t.choice, None)
                        delta = tuple(map(from_px, t.delta))

                        x = delta[0] - offset[0]
                        y = delta[1] - offset[1]
                        z = delta[2]

                        if color is None:
                            continue

                        if not (
                            x in range(0, size_of_image[0])
                            and y in range(0, size_of_image[1])
                        ):
                            raise Exception(
                                f"Unable to update {path}: {x, y} not within {size_of_image}"
                            )

                        images[path].putpixel((x, y), color)

                    path = join("world", str(e.id), "entitymap.png")
                    sizes[path] = size_of_image

                    if path not in images:
                        assert reference.dimensions != (0, 0)
                        images[path] = Image.new("RGBA", size_of_image)

                    for guid in self.units:
                        u = self.units[guid]

                        if guid in self.controlled:
                            continue

                        if u.anchor_id != e.id:
                            continue

                        color = (255, 0, 0)
                        delta = tuple(map(from_px, u.delta))

                        x = delta[0] - offset[0]
                        y = delta[1] - offset[1]
                        z = delta[2]

                        if not (
                            x in range(0, size_of_image[0])
                            and y in range(0, size_of_image[1])
                        ):
                            raise Exception(
                                f"Unable to update {path}: {x, y} not within {size_of_image}"
                            )

                        images[path].putpixel((x, y), color)

                    distances = {}
                    for edge in self.world.in_edges(e.id, data=True):
                        u, v, data = edge
                        distances[str(u)] = list(
                            map(from_px, tuple(-1 * _ for _ in data["delta"]))
                        )

                    data = {
                        "size": list(sizes[path]),
                        "radius": e.radius // SCALE,
                        "distances": distances,
                    }

                    with open(join(dirname(path), "meta.json"), "w") as f:
                        f.write(json.dumps(data))

                for path, img in images.items():
                    img.save(path)

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

            ref_id, _, edge = candidate
            pos = unit.relative(edge["delta"])

            total = math.dist((0, 0, 0), edge["delta"])
            old = int(math.dist((0, 0, 0), unit.delta))
            new = int(math.dist(unit.delta, edge["delta"]))

            midpoint = range(int(total * 0.33), int(total * 0.66))

            if old in midpoint:
                return self.transform(
                    ("units", unit.guid),
                    lambda e: e.set(
                        "overlaps",
                        [ref_id],
                    ),
                )

            if old < new:
                return self.transform(
                    ("units", unit.guid),
                    lambda e: e.set("overlaps", []),
                )

            return self.transform(
                ("units", unit.guid),
                lambda e: e.set("anchor_id", ref_id)
                .set("delta", pos)
                .set("overlaps", []),
            )

        def accessible(
            self, location: Location, relevant: typing.Iterable[Location]
        ) -> bool:
            x, y, _ = self.position(*location)
            return (x, y) in map(lambda e: (e[0], e[1]), relevant)

        def facing(self, unit: Unit) -> tuple[int, int, dict]:
            """which anchor is the unit facing

            ...
            """

            old = self.get_anchor(unit.anchor_id)

            def distance(tile: Tile) -> Location:
                edge = self.world[tile.anchor_id][unit.anchor_id]

                real1 = tile.delta
                real2 = unit.relative(edge["delta"])

                return math.dist(real2, real1)

            candidate = min(
                filter(lambda t: t.anchor_id != unit.anchor_id, self.tiles),
                key=distance,
                default=None,
            )

            if candidate is None:
                return None

            u, v = candidate.anchor_id, unit.anchor_id
            edge = (u, v, self.world[u][v])
            return edge

        def movements(self, keys: dict[int, bool], mx: int, my: int) -> "Game":
            target: Anchor | Unit | None = self.units[self.controlled[0]]

            if target.editor and any(
                filter(lambda e: e.name == "mover", target.effects)
            ):
                target = next(
                    filter(operator.attrgetter("targeted"), self.anchors), None
                )

                if target is None:
                    target = next(
                        filter(operator.attrgetter("targeted"), self.units.values()),
                        None,
                    )

            if isinstance(target, Unit):
                if not any(
                    [keys[k] for k in [pg.K_w, pg.K_s, pg.K_a, pg.K_d, pg.K_SPACE]]
                ):
                    return self.transform(
                        ("units", target.guid),
                        lambda e: e.set("state", "idle").set("stepped", 0),
                    )

                distance = target.distance()
                runner: Unit = target.set("state", "run").set(
                    "stepped", target.stepped + 1 if target.stepped < 100 else 6
                )

                if keys[pg.K_SPACE] and runner.jumped < 1:
                    runner = runner.set("jumped", 5).set(
                        "delta",
                        (target.delta[0], target.delta[1], target.delta[2] + 5),
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

                idx = self.anchors.index(target)
                u, v, data = min(
                    list(self.world.edges(target.id, data=True)),
                    key=lambda e: abs(e[2]["weight"]),
                )
                x, y, z = data["delta"]

                old = new = data["delta"]

                if keys[pg.K_w]:
                    new = (x, y - SCALE, z)
                if keys[pg.K_s]:
                    new = (x, y + SCALE, z)
                if keys[pg.K_a]:
                    new = (x - SCALE, y, z)
                if keys[pg.K_d]:
                    new = (x + SCALE, y, z)

                a = data.copy()
                a["delta"] = new
                a["weight"] = math.dist((0, 0, 0), a["delta"])

                b = data.copy()
                b["delta"] = tuple(-1 * e for e in new)
                b["weight"] = math.dist((0, 0, 0), b["delta"])

                self.world.add_edge(u, v, **a)
                self.world.add_edge(v, u, **b)

                for e in self.world.edges(v, data=True):
                    u1, v1, secondary = e
                    if u1 != v:
                        continue

                    if u == v1:
                        continue

                    one, other = (u, v1)
                    relation = v

                    first, second = (
                        self.world[one][relation]["delta"],
                        self.world[other][relation]["delta"],
                    )

                    delta = tuple(a - b for a, b in zip(first, second))
                    weight = math.dist((0, 0, 0), delta)
                    self.world.add_edge(one, other, weight=weight, delta=delta)

                    delta = tuple(-1 * e for e in delta)
                    weight = math.dist((0, 0, 0), delta)
                    self.world.add_edge(other, one, weight=weight, delta=delta)

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

        def notify(self, unit: PMap) -> "Game":
            return self

            with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sock:
                for e in [unit.anchor_id, *unit.overlaps]:
                    edge = self.world.get_edge_data(e, unit.anchor_id)
                    pos = None
                    if edge is not None:
                        pos = unit.relative(edge["delta"])

                    sock.sendto(
                        pickle.dumps(
                            [
                                e,
                                unit.overlaps,
                                unit.guid,
                                pos or unit.delta,
                                unit.o,
                                unit.state,
                                unit.health,
                                unit.stamina,
                                unit.name,
                                int(time.time()),
                            ]
                        ),
                        ("localhost", 8818),
                    )

                others = {}

                while True:
                    data, server = sock.recvfrom(1024)
                    if not data:
                        break

                    anchor_id, guid, delta, o, state, health, stamina, name, seen = (
                        pickle.loads(data)
                    )

                    others[guid] = Unit(
                        name=name,
                        guid=guid,
                        health=health,
                        stamina=stamina,
                        o=o,
                        state=state,
                        sprites=models[name],
                        delta=delta,
                        anchor_id=anchor_id,
                    )

                return self.set("others", others)

        def position(self, x: int, y: int, z: int):
            _x = to_px(from_px(x))
            _y = to_px(from_px(y))
            _z = to_px(from_px(z))

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
                            filter(
                                lambda e: concept and e.startswith(concept), ACTIONS
                            ),
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

        def get_anchor(self, nr: int) -> Anchor | None:
            if len(self.anchors) < nr:
                return None

            return self.anchors[nr - 1]

        def new_anchor(
            self,
            nr: int,
            data: dict,
            ref: int | None = None,
            delta: Location | None = None,
        ) -> Anchor:
            data["id"] = nr  # len(self.self.anchors) + 1

            if ref is not None and delta is not None:
                self.world.add_edge(
                    nr,
                    ref,
                    delta=delta,
                    weight=math.dist((0, 0, 0), delta),
                )

                inverse: Location = tuple(-1 * e for e in delta)

                self.world.add_edge(
                    ref, nr, delta=inverse, weight=math.dist((0, 0, 0), inverse)
                )

            return Anchor(**data)

        def make_anchor(self, unit: Unit) -> Anchor | None:
            params = [
                to_px(from_px(unit.delta[0])) - (10 * SCALE),
                to_px(from_px(unit.delta[1])) - (10 * SCALE),
                0,
            ]

            if any(
                e
                for e in self.tiles
                if e.delta == params and e.anchor_id == unit.anchor_id
            ):
                return None

            return self.new_anchor(
                len(self.anchors) + 1,
                dict(radius=4 * SCALE, enabled=True),
                unit.anchor_id,
                params,
            )

        def make_tile(self, unit: Unit) -> Tile | None:
            params = [-1]

            r = rebase = lambda v: to_px(from_px(v))
            _x, _y, _z = unit.delta

            match unit.o:
                case "S":
                    params = r(_x), r(_y) + SCALE, r(_z)
                case "E":
                    params = r(_x) + SCALE, r(_y), r(_z)
                case "W":
                    params = r(_x) - SCALE, r(_y), r(_z)
                case "N":
                    params = r(_x), r(_y) - SCALE, r(_z)

            if any(
                e
                for e in self.tiles
                if e.delta == params and e.anchor_id == unit.anchor_id
            ):
                return None

            return Tile(
                params,
                choice=COLORMAP.tile[(128, 64, 0)],
                sprites=models["ground"],
                anchor_id=unit.anchor_id,
            )

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

    started_at = pg.time.get_ticks()
    pg.init()

    screen = pg.display.set_mode((900, 600), pg.RESIZABLE)
    pg.display.set_caption("r/untitledMMORPG")

    cycles: dict[str, typing.Iterable] = {"ground_idle": itertools.cycle([])}
    frame: dict[str, typing.Any] = {}

    sources: dict[str, pg.image] = {
        "ground_idle": pg.image.load("tiles1.png").convert_alpha()
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
                raw,
                (
                    to_px(raw.width) / sprite_width,
                    to_px(raw.height) / sprite_height,
                ),
            )

            key = f"{model}_{mode}"
            cycles[key] = itertools.cycle(range(0, img.width, SCALE))
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
                (
                    "run",
                    functools.partial(pg.image.load, "critters/wolf/wolf-run.png"),
                ),
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
            (SCALE, 41),
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

    COLORMAP = NS(
        tile={
            (0, 255, 0): (2, 1),  # green
            (128, 64, 0): (1, 1),  # (4, 1),  # brown
            (128, 128, 128): (3, 1),  # gray
            (0, 0, 255): (4, 1),  # blue
        },
        entity={(255, 0, 0): models["wolf"]},
    )

    COLORMAP_R = NS(
        tile={t: c for c, t in COLORMAP.tile.items()},
        # entity={e: c for c, e in COLORMAP.entity.items()}
    )

    tiles = vec()
    units = m()

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

    camera = NS(x=0, y=0)

    player_anchor: int = 1  # assume this will be retrieved from someplace later on
    reference_anchor: int = (
        2  # assume one will always be loaded as a counterbalance for the player anchor
    )

    if False:
        pos = nx.spring_layout(world)

        nx.draw(g.world, pos, with_labels=True)
        nx.draw_networkx_edge_labels(
            world, pos, edge_labels=nx.get_edge_attributes(world, "delta")
        )

        # pyplot.show()
        sys.exit(0)

    g = Game(
        option=itertools.cycle(
            list(
                sorted(
                    [
                        (2, 1),  # green
                        (1, 1),  # (4, 1),  # brown
                        (3, 1),  # gray
                        (4, 1),  # blue
                    ],
                    # itertools.product(range(1, 12), range(1, 12)),
                    key=lambda e: e[1],
                )
            )
        ),
        model=itertools.cycle(["stag", "boar", "wolf"]),
        ticks=pg.time.get_ticks(),
        splash=True,
        night=(datetime.now().hour not in range(6, 18 + 1)),
        events=deque([]),
        running=True,
        targets=tuple(),
        anchors=vec(),
        tiles=vec(),
        character="stag",
        units=m(),
        others={},
        controlled=[],
        world=nx.DiGraph(),
    )

    for anchor_id in sorted(map(int, os.listdir("world"))):
        path = join("world", str(anchor_id))
        meta = join(path, "meta.json")

        tilemap = join(path, "tilemap.png")
        heightmap = join(path, "heightmap.png")
        entitymap = join(path, "entitymap.png")

        if not exists(meta):
            continue

        with open(meta, "r") as f:
            thing = json.loads(f.read())
            params = (anchor_id, dict(radius=SCALE * thing["radius"], enabled=True))
            additions = []

            for ref, delta in thing.get("distances", {}).items():
                additions.append((*params, int(ref), tuple(map(to_px, delta))))

            if not additions:
                additions = [params]

            loaded = g.anchors
            for addition in additions:
                anchor = g.new_anchor(*addition)

                if anchor.id in map(operator.attrgetter("id"), loaded):
                    continue

                loaded = loaded.append(anchor)

            g = g.set("anchors", loaded)

            _w, _h = tuple(thing["size"])

            _w = _w + _w % 2
            _h = _h + _h % 2

        if exists(tilemap):
            heights = {}

            if exists(heightmap):
                with Image.open(heightmap).convert("RGBA") as img:
                    for y in range(_h):
                        for x in range(_w):
                            vertical = None

                            with suppress(Exception):
                                vertical = img.getpixel((x, y))

                            if vertical is None:
                                continue

                            _r, _g, _b, _a = vertical

                            if not (_r == _g == _b):
                                continue

                            if x not in heights:
                                heights[x] = {}

                            heights[x][y] = _r - 128

            with Image.open(tilemap).convert("RGBA") as img:
                offset = (to_px(_w) // 2, to_px(_h) // 2)

                for y in range(_h):
                    for x in range(_w):
                        px = None

                        with suppress(Exception):
                            px = img.getpixel((x, y))

                        if px is None:
                            continue

                        _r, _g, _b, _a = px

                        if _a < 255:
                            continue

                        choice = COLORMAP.tile.get((_r, _g, _b), None)
                        if choice is None:
                            continue

                        z = 0
                        if heights:
                            z = heights[x][y]

                        tiles = tiles.append(
                            Tile(
                                delta=(to_px(x) - offset[0], to_px(y) - offset[1], z),
                                choice=choice,
                                sprites=models["ground"],
                                anchor_id=anchor_id,
                            )
                        )

            g.get_anchor(anchor_id).recentered(
                filter(lambda t: t.anchor_id == anchor_id, tiles)
            )

        if exists(entitymap):
            with Image.open(entitymap).convert("RGBA") as img:
                offset = (to_px(_w) // 2, to_px(_h) // 2)

                for y in range(_h):
                    for x in range(_w):
                        px = None

                        with suppress(Exception):
                            px = img.getpixel((x, y))

                        if px is None:
                            continue

                        _r, _g, _b, a = px

                        if _a < 255:
                            continue

                        char = COLORMAP.entity.get((_r, _g, _b), None)
                        if char is None:
                            continue

                        units = units.set(
                            str(uuid4()),
                            Unit(
                                delta=(to_px(x) - offset[0], to_px(y) - offset[1], 0),
                                sprites=char,
                                anchor_id=anchor_id,
                                stamina=123,
                                health=500,
                                name="asdf",
                            ),
                        )

    g = g.set("tiles", tiles).set("units", units)

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
        anchor_id=player_anchor,
        overlaps=[],
    )

    if False:  # if sys.argv[1] == "b":
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

    g = (
        g.set("units", g.units.set(p1.guid, p1))
        .set("controlled", [p1.guid])
        .set("running", True)
    )

    clock = pg.time.Clock()

    # state = threading.Thread(target=g.loop, daemon=True)
    # state.start()

    virtual = pg.Surface((640, 480))
    act = []

    last = pg.time.get_ticks()
    while g.running:
        tock = False
        now = pg.time.get_ticks()

        if now - last >= 100:
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

            g = g.transform(("units", guid), unit.set("jumped", max(0, unit.jumped - 1)))
            g = g.movements(pg.key.get_pressed(), *pg.mouse.get_pos())

            if tock:  # g.units[guid].stepped % 5 == 0:
                pass  # sound_step[next(foot)].play()

            g = g.anchoring()

            relevant = lambda presence, e: e.anchor_id in presence
            is_relevant = functools.partial(relevant, [g.units[guid].anchor_id])
            is_walkable = lambda t: t.choice not in [COLORMAP.tile.get((0, 0, 255))]

            legal: bool = g.accessible(
                g.units[guid].delta,
                map(
                    operator.attrgetter("delta"),
                    filter(is_walkable, filter(is_relevant, g.tiles)),
                ),
            )

            def at_tile(e):
                *p, _ = g.position(*g.units[guid].delta)
                *t, _ = e.delta

                return p == t

            at = next(
                filter(
                    at_tile,
                    filter(is_relevant, g.tiles),
                ),
                None,
            )

            if at is not None and (g.units[guid].delta[2] != at.delta[2]):
                *xy, z = g.units[guid].delta
                diff = at.delta[2] - z

                if not g.units[guid].jumped:
                    changed = tuple(xy) + (z + diff // 1.61803,)

                    g = g.set(
                        "units",
                        g.units.transform(
                            (
                                guid,
                                "delta",
                            ),
                            changed,
                        ),
                    )

            candidate = g.facing(g.units[guid])
            reachable = diff <= 8
            falling = diff < -8

            if candidate is not None:
                one, other, edge = candidate
                pos = g.units[guid].relative(edge["delta"])

                is_relevant = functools.partial(relevant, [other, one])

                possible = g.accessible(
                    pos,
                    map(
                        lambda e: e.delta,
                        filter(is_walkable, filter(is_relevant, g.tiles)),
                    ),
                )
                legal = (legal or possible) and reachable

            if falling:
                g = g.set(
                    "units",
                    g.units.transform((guid, "health"), g.units[guid].health - 1),
                )

            if not legal:
                g = g.set("units", g.units.set(guid, initial))

            act, g = g.act(act)

            tile = []
            if g.units[guid].editor:
                tile = [
                    e
                    for e in g.tiles
                    if e.anchor_id == g.units[guid].anchor_id
                    and g.accessible(g.units[guid].delta, iter([e.delta]))
                ]

            targets = tuple(
                set(
                    map(
                        operator.attrgetter("guid"),
                        itertools.chain(
                            tile, g.units.values(), g.others.values(), g.anchors
                        ),
                    )
                )
            )

            if g.targets != targets:
                g = g.set("targets", targets).set("cycle", itertools.cycle(targets))

            g = g.controls(
                pg.key.get_pressed(),
                *pg.mouse.get_pos(),
                pg.mouse.get_pressed(),
                screen,
            )
            g = g.effects()

        if pg.time.get_ticks() % 2000:
            g = g.notify(g.units[g.controlled[0]])

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

        for e in g.elements(virtual):
            if e.type == "IMAGE":
                virtual.blit(e.obj, e.rect)

            if e.type == "RECT":
                pg.draw.rect(virtual, e.color, e.rect)

            if e.type == "ELLIPSE":
                pg.draw.ellipse(virtual, e.color, e.rect, e.width)

        scaled = pg.transform.scale(virtual, (screen.width, screen.height))

        screen.blit(scaled, (0, 0))

        pg.display.flip()
        clock.tick(9)
        await asyncio.sleep(0)

    # state.join()
    pg.quit()


if __name__ == "__main__":
    asyncio.run(main())
