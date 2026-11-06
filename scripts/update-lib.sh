#!/usr/bin/env bash
# scripts/update-lib.sh
#
# Regenerate the umbrella module of each library from its Lean files: the tracked ones and new ones
# that are not ignored, in byte order of their module names. This needs no Lake, so the umbrella
# check can run in a job with no build.
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

library_modules() {
  git -c core.quotePath=false ls-files --cached --others --exclude-standard -- "$1/*.lean" |
    while IFS= read -r file; do
      if [[ -f "$file" ]]; then
        printf '%s\n' "${file%.lean}"
      fi
    done |
    tr '/' '.' |
    LC_ALL=C sort -u
}

# Active root umbrellas are module files with public imports.
for library in ToMathlib VCVio VCVioCslib LatticeCrypto Extern HashSig Examples VCVioWidgets VCVioTest; do
  {
    printf 'module  -- shake: keep-all --deprecated_module: ignore\n\n'
    library_modules "$library" | sed 's/^/public import /'
  } > "$library.lean"
done

# Interop is dormant and has not yet adopted module scopes.
library_modules Interop | sed 's/^/import /' > Interop.lean
