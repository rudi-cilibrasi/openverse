#!/usr/bin/env bash
# A later cast must not make unrelated nested call errors exponential.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ov="$root/.lake/build/bin/openverse"
cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
# This is a hang guard, not a wall-clock ratio: valid work may share a host.
limit="${REFINE_HINT_TIMEOUT:-60}"
for n in 24 48 96; do
  python3 -I - "$n" "$tmp/invalid.verse" <<'PY'
import pathlib,sys
n=int(sys.argv[1])
body="Wrap("*n+"Need(1,?Index:=dup[P].Index)"+")"*n
pathlib.Path(sys.argv[2]).write_text("pair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){Index:int=0}\nWrap(X:int):int=X\nNeed(X:string,?Index:int=0):int=Index\nF(P:pair(a,b) where a:type,b:type)<decides>:int="+body+"\nMain():void={}\n")
PY
  status=0
  (ulimit -v 4194304; timeout "$limit" "$ov" check "$tmp/invalid.verse") >"$tmp/out" 2>"$tmp/err" || status=$?
  if [[ $status != 4 ]] || ! grep -qF 'expected string, found int' "$tmp/err"; then
    echo "FAIL refinement recovery: $n invalid wrappers, status $status"
    cat "$tmp/err"
    exit 1
  fi
done
printf 'int 9\nstring right\nexit=0\n' >"$tmp/want"
for n in 24 64; do
  python3 -I - "$n" "$tmp/valid.verse" <<'PY'
import pathlib,sys
n=int(sys.argv[1])
body="Wrap("*n+"Echo(P.A,?Other:=dup[P].B)"+")"*n
pathlib.Path(sys.argv[2]).write_text('pair(a:type,b:type):=class{A:a;B:b}\ndup(t:type):=class(pair(t,t)){}\nWrap(X:t where t:type):t=X\nEcho(X:t,?Other:t=X where t:type):t=Other\nF(P:pair(a,b) where a:type,b:type)<decides>:b='+body+'\nMain():void=\n    if(V:=F[dup(int){A:=7,B:=9}])then Print("int {V}")else Print("wrong")\n    if(V:=F[dup(string){A:="left",B:="right"}])then Print("string {V}")else Print("wrong")\n')
PY
  { (ulimit -v 4194304; timeout "$limit" "$ov" run "$tmp/valid.verse" --emit "$tmp/p.vbc"); echo "exit=$?"; } >"$tmp/lean"
  { timeout "$limit" "$cv" "$tmp/p.vbc"; echo "exit=$?"; } >"$tmp/c"
  cmp "$tmp/want" "$tmp/lean"
  cmp "$tmp/want" "$tmp/c"
done
echo "refinement hint probes: 3 bounded invalid depths and 2 valid depths in both VMs passed"
