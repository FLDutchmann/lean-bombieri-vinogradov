#!/usr/bin/env bash

lake build :blueprint

uv run leanblueprint web
uv run leanblueprint serve