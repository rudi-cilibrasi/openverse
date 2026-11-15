#!/usr/bin/env bash
# A later cast must not make unrelated nested call errors exponential.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ov="$root/.lake/build/bin/openverse"
cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
# This is a hang guard, not a wall-clock ratio: valid work may share a host.
limit="${REFINE_HINT_TIMEOUT:-60}"
for shape in scalar map; do
for n in 24 48 96; do
  python3 -I - "$n" "$tmp/invalid.verse" "$shape" <<'PY'
import pathlib,sys
n=int(sys.argv[1])
body="Wrap("*n+"Need(1,?Index:=dup[P].Index)"+")"*n
shape=sys.argv[3]
if shape=="map":body="map{Empty()=>"+body+"}"
ret="[?int]int" if shape=="map" else "int"
pathlib.Path(sys.argv[2]).write_text("Empty(?Default:?t=false where t:type):?t=Default\npair(a:type,b:type):=class{}\ndup(t:type):=class(pair(t,t)){Index:int=0}\nWrap(X:int):int=X\nNeed(X:string,?Index:int=0):int=Index\nF(P:pair(a,b) where a:type,b:type)<decides>:"+ret+"="+body+"\nMain():void={}\n")
PY
  status=0
  (ulimit -v 4194304; timeout "$limit" "$ov" check "$tmp/invalid.verse") >"$tmp/out" 2>"$tmp/err" || status=$?
  diagnostic=0
  grep -qF 'expected string, found int' "$tmp/err" && diagnostic=1
  # The frozen parent reports the contextual-key refusal for this invalid
  # map; either retained refusal must remain bounded.
  if [[ $shape == map ]] && grep -qF 'cannot infer type parameter t of Empty' "$tmp/err"; then diagnostic=1; fi
  if [[ $status != 4 || $diagnostic != 1 ]]; then
    echo "FAIL refinement recovery: $n invalid wrappers, status $status"
    cat "$tmp/err"
    exit 1
  fi
done
done
printf 'int 9\nstring right\nexit=0\n' >"$tmp/want"
for shape in scalar map; do
for n in 24 64; do
  python3 -I - "$n" "$tmp/valid.verse" "$shape" <<'PY'
import pathlib,sys
n=int(sys.argv[1])
body="Wrap("*n+"Echo(P.A,?Other:=dup[P].B)"+")"*n
shape=sys.argv[3]
ret='[?int]b' if shape=='map' else 'b'
if shape=='map':body='map{Empty()=>'+body+'}'
source='Empty(?Default:?t=false where t:type):?t=Default\npair(a:type,b:type):=class{A:a;B:b}\ndup(t:type):=class(pair(t,t)){}\nWrap(X:t where t:type):t=X\nEcho(X:t,?Other:t=X where t:type):t=Other\nF(P:pair(a,b) where a:type,b:type)<decides>:'+ret+'='+body+'\nMain():void=\n    if(V:=F[dup(int){A:=7,B:=9}])then Print("int {V}")else Print("wrong")\n    if(V:=F[dup(string){A:="left",B:="right"}])then Print("string {V}")else Print("wrong")\n'
if shape=='map':source=source.replace('if(V:=F[','if(M:=F[').replace('}])then','}],V:=M[false])then')
pathlib.Path(sys.argv[2]).write_text(source)
PY
  { (ulimit -v 4194304; timeout "$limit" "$ov" run "$tmp/valid.verse" --emit "$tmp/p.vbc"); echo "exit=$?"; } >"$tmp/lean"
  { timeout "$limit" "$cv" "$tmp/p.vbc"; echo "exit=$?"; } >"$tmp/c"
  cmp "$tmp/want" "$tmp/lean"
  cmp "$tmp/want" "$tmp/c"
done
done
# These are nested literals, rather than nested calls inside one map.
for n in 8 16 32; do
  python3 -I - "$n" "$tmp/nested-invalid.verse" "$tmp/nested-valid.verse" <<'PYMAP'
import pathlib,sys
n=int(sys.argv[1]);keys=['?int' if i%2==0 else '?string' for i in range(n)]
pre='pair(a:type,b:type):=class{A:a;B:b}\ndup(t:type):=class(pair(t,t)){Index:int=0}\nEmpty(?Default:?t=false where t:type):?t=Default\nNeed(X:string,?Index:int=0):int=Index\nEcho(X:t,?Other:t=X where t:type):t=Other\n'
nest=lambda leaf:'map{Empty()=>'*n+leaf+'}'*n
ret=''.join('['+key+']' for key in keys)
pathlib.Path(sys.argv[2]).write_text(pre+'F(P:pair(a,b) where a:type,b:type)<decides>:'+ret+'int='+nest('Need(1,?Index:=dup[P].Index)')+'\nMain():void={}\n')
source=pre+'F(P:pair(a,b) where a:type,b:type)<decides>:'+ret+'b='+nest('Echo(P.A,?Other:=dup[P].B)')+'\nMain():void=\n'
for ty,a,b,label in [('int','7','9','int'),('string','"left"','"right"','string')]:
 clauses=['M0:=F[dup('+ty+'){A:='+a+',B:='+b+'}]']+['M'+str(i+1)+':=M'+str(i)+'[false]' for i in range(n)]
 source+='    if('+','.join(clauses)+')then Print("'+label+' {M'+str(n)+'}")else Print("wrong")\n'
pathlib.Path(sys.argv[3]).write_text(source)
PYMAP
  status=0
  (ulimit -v 4194304; timeout "$limit" "$ov" check "$tmp/nested-invalid.verse") >"$tmp/out" 2>"$tmp/err" || status=$?
  if [[ $status != 4 ]] || ! grep -qF 'expected string, found int' "$tmp/err"; then
    echo "FAIL nested map recovery: $n literals, status $status"
    cat "$tmp/err"
    exit 1
  fi
  { (ulimit -v 4194304; timeout "$limit" "$ov" run "$tmp/nested-valid.verse" --emit "$tmp/p.vbc"); echo "exit=$?"; } >"$tmp/lean"
  { timeout "$limit" "$cv" "$tmp/p.vbc"; echo "exit=$?"; } >"$tmp/c"
  cmp "$tmp/want" "$tmp/lean"
  cmp "$tmp/want" "$tmp/c"
done
echo "refinement hint probes: 9 bounded invalid cases and 7 valid cases in both VMs passed"
