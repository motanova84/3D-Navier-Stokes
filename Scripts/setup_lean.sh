#!/usr/bin/env bash
set -euxo pipefail
# Instala elan (gestor de Lean) si no está
if ! command -v elan &> /dev/null; then
  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
  export PATH="$HOME/.elan/bin:$PATH"
fi
echo "elan version:"
elan --version
# Descarga cachés de mathlib (opcional si usas caché CI)
