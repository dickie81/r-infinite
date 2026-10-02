#!/usr/bin/env bash
# Build the Davenport–Heilbronn layer (rounds 253–273; split from src/ in round 275) into ../../build.
# Usage: ./build.sh, after ../../build.sh. Set MATHLIB, JOBS and FORCE as for ../../build.sh, which this
# runs with SRC set to this directory; a file is rebuilt when it or anything it imports changed,
# including pilot modules.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
SRC="$HERE" exec "$HERE/../../build.sh"
