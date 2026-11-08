#!/usr/bin/env bash
# A git worktree for a branch, ready to work in. The Lean build is copied from this checkout, so
# `lake build` rebuilds only the modules that differ: a couple of minutes instead of a full build.
#   usage: scripts/worktree.sh BRANCH [DIR]
# DIR defaults to ../openverse-<last part of BRANCH>. An existing local or remote branch is checked
# out; otherwise BRANCH is created from origin/main.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
branch="${1:?usage: scripts/worktree.sh BRANCH [DIR]}"
dir="${2:-$(dirname "$root")/openverse-${branch##*/}}"
git -C "$root" fetch -q origin
if git -C "$root" rev-parse -q --verify "refs/heads/$branch" >/dev/null; then
  git -C "$root" worktree add "$dir" "$branch"
elif git -C "$root" rev-parse -q --verify "refs/remotes/origin/$branch" >/dev/null; then
  git -C "$root" worktree add --track -b "$branch" "$dir" "origin/$branch"
else
  git -C "$root" worktree add -b "$branch" "$dir" origin/main
fi
if [[ -d "$root/.lake" ]]; then cp -a --reflink=auto "$root/.lake" "$dir/.lake"; fi
cd "$dir"
lake build 2>&1 | tail -1
make -s -C runtime
echo "worktree.sh: $dir on $branch"
