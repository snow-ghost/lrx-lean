#!/usr/bin/env bash
# Reproducible check of the publication package.
set -euo pipefail
cd "$(dirname "$0")/.."
echo "== source integrity"; sha256sum --quiet -c files.sha256
echo "== forbidden constructs"; python3 scripts/check_forbidden.py .
echo "== build"; lake build LRXDiameter Solution Challenge
echo "== axiom audit"; lake env lean Verify.lean
