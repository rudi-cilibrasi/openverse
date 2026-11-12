#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
exec python3 "$root/tests/scripts/test-float-math.py" "${1:-64}" "${2:-1}"
