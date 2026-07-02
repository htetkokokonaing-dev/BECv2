#!/usr/bin/env bash
set -euo pipefail

echo "[BEC v2.0] full source check"

echo
echo "[1/4] Lean version"
lean --version

echo
echo "[2/4] Lake build"
lake build

echo
echo "[3/4] Blocked-token scan"
./scripts/blocked_token_scan.sh

echo
echo "[4/4] Root import check"
lake env lean BECv2.lean

echo
echo "PASS: BECv2 source package checked successfully."
