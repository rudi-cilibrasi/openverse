#!/usr/bin/env bash
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
exec python3 "$root/tests/scripts/test-refining-contexts.py" "${1:-144}" "${2:-1}" gadt_waiting_contexts.py
