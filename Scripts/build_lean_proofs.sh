#!/usr/bin/env bash
set -euxo pipefail
export PATH="$HOME/.elan/bin:$PATH"
# Construye todo el proyecto
lake update
lake build
