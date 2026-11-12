#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
exec python3 "$root/tests/scripts/test-call-packing.py" "${1:-60}" "${2:-1}"
