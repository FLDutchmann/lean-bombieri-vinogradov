#!/usr/bin/env bash

# Compile and serve the web version of the blueprint.

lake build :blueprint

uv run leanblueprint web
uv run leanblueprint serve