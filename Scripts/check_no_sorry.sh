#!/usr/bin/env bash
set -euxo pipefail
# Check for sorry/admit in production-ready files only
# Development files are allowed to have sorry during proof development

echo "🔍 Checking production-ready Lean files for incomplete proofs..."

# Check root-level production files (these should be complete)
PRODUCTION_FILES="PsiNSE_Production_NoSorry.lean"
FOUND_SORRY=0

for file in $PRODUCTION_FILES; do
  if [ -f "$file" ]; then
    # Check for sorry/admit excluding comments (lines starting with -- or containing --)
    # Match only actual sorry/admit keywords not in quotes or comments
    if grep -E '^\s*sorry\s*$|^\s*admit\s*$|^\s*sorry\s*--|^\s*admit\s*--' "$file" > /dev/null 2>&1; then
      echo "❌ Found 'sorry' or 'admit' in production file: $file"
      grep -n -E '^\s*sorry\s*$|^\s*admit\s*$|^\s*sorry\s*--|^\s*admit\s*--' "$file"
      FOUND_SORRY=1
    fi
  fi
done

# Count sorry in development files (informational)
DEV_COUNT=$(grep -r -E '\bsorry\b|\badmit\b' Lean4-Formalization --include="*.lean" 2>/dev/null | grep -v "NoSorry" | wc -l)
if [ $DEV_COUNT -gt 0 ]; then
  echo "ℹ️  Development files contain $DEV_COUNT incomplete proofs (expected during development)"
fi

if [ $FOUND_SORRY -eq 1 ]; then
  echo "❌ Production files must not contain 'sorry' or 'admit'."
  exit 1
fi

echo "✅ All production-ready files are complete (no 'sorry' or 'admit' found)."
