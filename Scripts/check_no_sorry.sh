#!/usr/bin/env bash
set -euxo pipefail
# 1) Opcional: avisos de sorry como error en compilación
#   (Se puede reforzar con opciones a nivel de archivo: set_option warnSorry true)
# 2) Escaneo de texto como red de seguridad:
if grep -R --line-number -E '\bsorry\b|\badmit\b' Lean4-Formalization || \
   grep -R --line-number -E '\bsorry\b|\badmit\b' ./*.lean ; then
  echo "❌ Found 'sorry' or 'admit' in sources."
  exit 1
fi
echo "✅ No 'sorry' or 'admit' found."
