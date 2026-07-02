#!/usr/bin/env bash
set -euo pipefail

echo "[BEC v2.0] full source check"

if [ ! -f lakefile.toml ] && [ ! -f lakefile.lean ]; then
  echo "ERROR: run this script from the repository root."
  exit 1
fi

echo
echo "[1/4] Lean version"
lake env lean --version

echo
echo "[2/4] Root import check"
lake env lean BECv2.lean

echo
echo "[3/4] Individual module check"
for f in BECv2/*.lean; do
  echo "checking $f"
  lake env lean "$f"
done

echo
echo "[4/4] Blocked-token scan"
./scripts/blocked_token_scan.sh

echo
echo "PASS: BECv2 source tree compiled and blocked-token scan is clean."
