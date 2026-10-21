#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p verification/report-build
# Pass an absolute Tectonic binary as argument 1 when it is not on PATH.
"${1:-tectonic}" --keep-logs --outdir verification/report-build report/latex/main.tex
cp verification/report-build/main.pdf report/Maxwell_MGF_Report.pdf
cp verification/report-build/main.log verification/report-build.log
