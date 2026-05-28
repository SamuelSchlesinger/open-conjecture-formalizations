#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

python3 -m py_compile research/gilmer_ahs_verification.py research/window_experiment.py
python3 research/gilmer_ahs_verification.py \
  --check-ahs-certificate research/ahs_hinge_certificate.json
python3 research/window_experiment.py \
  --check-center-certificate research/center_generation_certificate.json
python3 research/window_experiment.py \
  --check-center-certificate research/reduced_maximal_center_generation_certificate.json
python3 research/window_experiment.py \
  --check-tc-summary research/tc_exact_n4_size7_summary.json
python3 research/window_experiment.py --campaign frontier-shadow
lake build
