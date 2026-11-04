#!/usr/bin/env bash
# Re-check the QuickProof theorems of proofs/quickproof/*/ (adapted from LeanOS ADR 0030).
#
# QuickProof (PolyForm Noncommercial) and CompCert (INRIA Non-Commercial) are not part of the
# build: this script runs the published Docker image on demand. For each project it makes a
# QuickProof workspace whose upstream is this repository at the project's pinned COMMIT, runs
# `qp check` with --check, then `qp assemble` (the frozen contract), copies the checked-in proof
# sources over it, commits them and runs `qp verify`, which must print PASS.
#
# usage: scripts/check-quickproof.sh [--check] [--keep DIR] [PROJECT...]
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
image="${OPENVERSE_QUICKPROOF_IMAGE:-ghcr.io/genproof/quickproof@sha256:8d420bf40775d63aecf9475135e37167e1c1f96183617b853d9eac806aa6961a}"
check=0; keep=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --check) check=1; shift ;;
    --keep) keep="$2"; shift 2 ;;
    *) break ;;
  esac
done
projects=("$@")
if [[ ${#projects[@]} -eq 0 ]]; then
  for d in "$root"/proofs/quickproof/*/; do [[ -d "$d/project" ]] && projects+=("$(basename "$d")"); done
fi
command -v docker >/dev/null || { echo "error: docker is required" >&2; exit 1; }
if [[ -n "$keep" ]]; then work="$keep"; mkdir -p "$work"; else
  work="$(mktemp -d "${TMPDIR:-/tmp}/openverse-quickproof.XXXXXX")"; trap 'rm -rf "$work"' EXIT; fi
mkdir -p "$work/home" "$work/ws/projects"

qp() {  # run a shell command in the image, with this repository mounted read-only
  docker run --rm -i --user "$(id -u):$(id -g)" \
    -e HOME="$work/home" -e XDG_CACHE_HOME="$work/home/.cache" -e QP_CACHE="$work/home/.cache/quickproof" \
    -e QP_WORKSPACE="$work/ws" -e QP_JOBS \
    -e GIT_AUTHOR_NAME=openverse -e GIT_AUTHOR_EMAIL=openverse@localhost \
    -e GIT_COMMITTER_NAME=openverse -e GIT_COMMITTER_EMAIL=openverse@localhost \
    -e GIT_CONFIG_COUNT=1 -e GIT_CONFIG_KEY_0=safe.directory -e GIT_CONFIG_VALUE_0='*' \
    -v "$work:$work" -v "$root:$root:ro" -w "$work/ws" \
    --entrypoint /bin/bash "$image" -lc "$1"
}

for name in "${projects[@]}"; do
  exp="$root/proofs/quickproof/$name"
  [[ -d "$exp/project" ]] || { echo "error: $exp has no project/" >&2; exit 1; }
  pname="openverse_$name"
  project="$work/ws/projects/$pname"
  rm -rf "$project"; cp -r "$exp/project" "$project"
  sed -i "s|^UPSTREAM=.*|UPSTREAM=$root|" "$project/project.conf"
  if [[ "$check" -eq 1 ]]; then
    qp "qp check $pname"
    mkdir -p "$root/build/quickproof/$name"
    cp "$project/CHECK.md" "$root/build/quickproof/$name/CHECK.md"
    echo "$name: qp check done (report: build/quickproof/$name/CHECK.md)"
  fi
  if [[ -d "$exp/proof" ]]; then
    repo="$work/$pname-proof"
    rm -rf "$repo"
    qp "qp assemble $pname $repo >/dev/null"
    cp -r "$exp/proof/." "$repo/"
    qp "cd $repo && git add -A src && git commit -qm 'openverse proof of $name' && qp verify --brief ."
  fi
done
