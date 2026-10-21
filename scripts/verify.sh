#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification
lake env lean --version > verification/lean-version.txt
lake build > verification/build.log 2>&1
lake env lean AxiomAudit.lean > verification/axioms.log 2>&1
python3 scripts/check_sources.py > verification/source-check.log
cat verification/source-check.log
