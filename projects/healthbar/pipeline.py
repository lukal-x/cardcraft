import bpy
import bmesh
import math
import random

from pyrsistent import PClass, PMap, field, m, v as vec

PROFILES = {
    "concrete": {"base_color": (0.4, 0.4, 0.4, 1.0), "roughness": 0.7, "specular": 0.3},
    "dirt": {"base_color": (0.25, 0.15, 0.08, 1.0), "roughness": 0.9, "specular": 0.1},
    "grass": {
        "base_color": (0.12, 0.35, 0.08, 1.0),
        "roughness": 0.85,
        "specular": 0.2,
    },
    "water": {"base_color": (0.05, 0.3, 0.5, 1.0), "roughness": 0.05, "specular": 1.0},
}


class Apparatus(PClass):
    sunlight: float = field(type=float, initial=2.5)
    rotation: tuple[float, float, float] = field(
        type=tuple, initial=(math.radians(45), math.radians(0), math.radians(135))
    )

    cam_at: tuple[float, float, float] = field(type=tuple, initial=(10.0, -10.0, 8.165))
    cam_angle: tuple[float, float, float] = field(
        type=tuple, initial=(math.radians(60), math.radians(0.0), math.radians(45.0))
    )

    cam_zoom: float = field(type=float, initial=6.0)


class Asset(PClass):
    id: str = field(type=str, initial=lambda: random.randbytes(6).hex())
    at: tuple[float, float, float] = field(type=tuple)
    faces: list = field(type=list)
    material_type: str = field(type=str, initial="abcd")
    profile: str = field(type=str, initial="water")
    vertices: list = field(type=list)


class Project(PClass):
    apparatus = field(type=Apparatus)
    assets: list[Asset] = field(type=list, initial=[])


def render(project: Project):
    # clear
    if bpy.ops.object.mode_set.poll():
        bpy.ops.object.mode_set(mode="OBJECT")

    for obj in bpy.data.objects:
        bpy.data.objects.remove(obj, do_unlink=True)

    for t in ["meshes", "materials", "cameras", "lights"]:
        ref = getattr(bpy.data, t)
        for e in ref:
            getattr(ref, "remove")(e)

    # setup
    scene = bpy.context.scene

    bpy.context.scene.render.image_settings.file_format = "PNG"
    bpy.context.scene.render.image_settings.color_mode = "RGBA"

    obj = bpy.data.objects.get("Cube")

    scene.use_nodes = True

    scene.render.resolution_x = 32
    scene.render.resolution_y = 64
    scene.render.resolution_percentage = 100

    scene.render.film_transparent = True
    scene.render.filter_size = 0.01

    # camera
    camera = bpy.data.cameras.new(name="IsoCamera")
    camera.type = "ORTHO"
    camera.ortho_scale = project.apparatus.cam_zoom

    # @todo: necessary?
    camera.shift_y = -0.125

    cam = bpy.data.objects.new(name="IsoCamera", object_data=camera)

    bpy.context.scene.camera = cam

    cam.location = project.apparatus.cam_at
    cam.rotation_euler = project.apparatus.cam_angle

    # lights
    solar = bpy.data.lights.new(name="IsoSun", type="SUN")
    solar.energy = project.apparatus.sunlight

    sun = bpy.data.objects.new(name="IsoSun", object_data=solar)
    bpy.context.collection.objects.link(sun)

    sun.rotation_euler = project.apparatus.rotation

    # assets
    for asset in project.assets:
        mesh = bpy.data.meshes.new(name=asset.id)
        mesh.from_pydata(asset.vertices, [], asset.faces)
        mesh.update()

        obj = bpy.data.objects.new(asset.id, mesh)
        bpy.context.collection.objects.link(obj)

        obj.location = asset.at

        name = asset.material_type
        mat = bpy.data.materials.get(name)

        if not mat:
            mat = bpy.data.materials.new(name=name)
            mat.use_nodes = True

        nodes = mat.node_tree.nodes
        principled = nodes.get("Principled BSDF")
        if principled:
            principled.inputs["Base Color"].default_value = PROFILES[asset.profile][
                "base_color"
            ]
            principled.inputs["Roughness"].default_value = PROFILES[asset.profile][
                "roughness"
            ]
            principled.inputs["Specular IOR Level"].default_value = PROFILES[
                asset.profile
            ]["specular"]

        obj.data.materials.append(mat)

    scene.render.filepath = "/tmp/scene.png"

    bpy.ops.render.render(write_still=True)


if __name__ == "__main__":
    half = 2.0 / 2.0

    cube = Asset(
        at=(0, 0, 0),
        faces=[
            (0, 1, 2, 3),
            (4, 7, 6, 5),
            (0, 4, 5, 1),
            (1, 5, 6, 2),
            (2, 6, 7, 3),
            (3, 7, 4, 0),
        ],
        vertices=[
            (-half, -half, -half),
            (half, -half, -half),
            (half, half, -half),
            (-half, half, -half),
            (-half, -half, half),
            (half, -half, half),
            (half, half, half),
            (-half, half, half),
        ],
    )

    projects = [
        Project(
            apparatus=Apparatus(),
            assets=[cube],
        )
    ]

    for project in projects:
        render(project)
