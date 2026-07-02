#!/usr/bin/env bash
set -euo pipefail

if grep -RInE '(^|[^A-Za-z])(sorry|admit|axiom|unsafe)([^A-Za-z]|$)' BECv2 BECv2.lean; then
  echo "ERROR: blocked token found."
  exit 1
else
  echo "PASS: blocked-token scan clean."
fi
