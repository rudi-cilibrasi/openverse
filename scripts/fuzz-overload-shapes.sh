#!/usr/bin/env bash
# Overload domain rules across contexts, orders and generic patterns.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec python3 "$root/tests/scripts/test-overload-shapes.py" "${1:-546}" "${2:-1}"
