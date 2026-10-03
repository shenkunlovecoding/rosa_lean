#!/bin/sh
# Build the run-compressed formalization via Lake (Lean 4.33.1, Std-only).
# No Mathlib, so this is seconds, not hours.
set -e
cd "$(dirname "$0")"
lake build
echo "ALL_LEAN_OK"
