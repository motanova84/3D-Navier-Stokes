#!/usr/bin/env bash
set -euxo pipefail
# Linter básico: sin imports huérfanos ni warnings fatales
# (Amplía con lake exe si añades herramientas de lint externas)
lake build
