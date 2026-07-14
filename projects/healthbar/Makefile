#!make

.PHONY: pygbag sprites

pygbag:
	.venv/bin/pygbag --archive .

sprites:
	blender -b -P pipeline.py
