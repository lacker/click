#!/usr/bin/env python3
"""Materialize the local compile database for this portable C++ example."""

import json
from pathlib import Path


project = Path(__file__).resolve().parent
template = json.loads((project / "compile_commands.json.in").read_text())
for command in template:
    if command["directory"] != "@PROJECT_ROOT@":
        raise ValueError("unexpected C++ example compilation directory")
    command["directory"] = str(project)
(project / "compile_commands.json").write_text(json.dumps(template, indent=2) + "\n")
