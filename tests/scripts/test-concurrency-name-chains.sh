#!/usr/bin/env bash
# Chains of calls of the program's own method named as a method of events and
# tasks is (#773): `X.Signal().Signal()…`, and so with Cancel, Await and
# Subscribe. A call `X.Signal()`, `X.Cancel()`, `X.Await()` or `X.Subscribe(F)`
# is an event's or a task's when `X` is one, so the receiver is elaborated to
# see what it is. Each question elaborated it for itself (whether it is a value
# of a type parameter that has the method, then whether it is a task or an
# event), and the call that is the program's own elaborated it again: three
# times at each call of Signal, Cancel and Await, twice at Subscribe, each
# making as many of the call before. Twelve calls took ten seconds, and
# twenty-four would not end. The receiver is elaborated once now, for all of
# those questions and for the call (`elabMemberApp`).
# Here: every shape of such a chain at twenty-four and ninety-six calls, each
# printing what its calls make, which says which method each call was; and the
# chains that are refused, with the error the chain of three calls is refused
# with. Each within a limit that is a guard against never ending and no measure
# of speed: a chain of ninety-six takes a tenth of a second.
# And chains of an event's and a task's own Await (#775), `E.Await().Await()…`
# of an event of events, or a task of tasks: the call becomes a call of a helper
# with the receiver as its argument, `$EvAwait(E)`, which elaborated the
# receiver a second time, twice as long for each call, and left the slots of
# the first behind, so that sixteen calls made a program the C runtime does not
# load. The helper takes the receiver as it is elaborated. Twenty-four and
# forty-eight deep, in both runtimes; and those that are refused, among them the
# chain asked for at a type it does not give, where the receiver is elaborated
# again at the type asked for, as it was, once for each call.
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
ov="$root/.lake/build/bin/openverse"
cv="$root/runtime/build/cverse"
tmp="$(mktemp -d)"; trap 'rm -rf "$tmp"' EXIT
limit="${CONCURRENCY_NAME_CHAIN_TIMEOUT:-60}"
python3 -I - "$tmp" <<'PY'
import sys
out = sys.argv[1]
# the method, how it is called, the letter it appends
SIGNAL, CANCEL, AWAIT = ('Signal', '', 's'), ('Cancel', '', 'c'), ('Await', '', 'a')
SUBSCRIBE = ('Subscribe', '7', '7')
ALL = [SIGNAL, CANCEL, AWAIT, SUBSCRIBE]
def decl(m, t, fx='', new=None, pre='', ov=''):
    name, arg, letter = m
    new = new or (lambda e: f'{t}{{T := {e}}}')
    return f'    {name}{ov}({"N:int" if arg else ""}){fx}:{t} =\n{pre}        ' + new('"{T}%s"' % letter) + '\n'
def cls(ms, t='trail', **kw):
    return f'{t} := class:\n    T:string = ""\n' + ''.join(decl(m, t, **kw) for m in ms)
def calls(ms, n, o='(', c=')', before=''):
    picked = [ms[(i * i + i // 3) % len(ms)] for i in range(n)]
    return (''.join(f'{before}.{name}{o}{arg}{c}' for name, arg, _ in picked), ''.join(l for _, _, l in picked))
# (an event of the program's, so that the events' own methods are there to be
# asked about: `Subscribe` of an event is asked only then)
EVENT = ('Tick():void = Print("tick")\nUse():void =\n    E := event(){}\n    S := E.Subscribe(Tick)\n'
         '    E.Signal()\n    S.Cancel()\n')
def main(e, pre='    X := trail{}\n', fx=''): return f'Main(){fx}:void =\n' + pre + f'    Print({e})\n'
def chains(n):
    s = {}
    for m in ALL:
        ch, want = calls([m], n)
        s[m[0].lower()] = (EVENT + cls([m]) + main(f'X{ch}.T'), want)
    ch, want = calls(ALL, n)
    s['all-four'] = (EVENT + cls(ALL) + main(f'X{ch}.T'), want)
    # without an event or a task anywhere in the program
    ch3, want3 = calls([SIGNAL, CANCEL, AWAIT], n)
    s['no-event'] = (cls([SIGNAL, CANCEL, AWAIT]) + main(f'X{ch3}.T'), want3)
    s['suspends'] = (cls([SIGNAL, CANCEL, AWAIT], fx='<suspends>', pre='        Sleep(0.0)\n')
                     + main(f'X{ch3}.T', fx='<suspends>'), want3)
    def failable(most):
        return cls([SIGNAL, CANCEL, AWAIT], fx='<decides><transacts>', pre=f'        T.Length < {most}\n')
    chf, wantf = calls([SIGNAL, CANCEL, AWAIT], n, o='[', c=']')
    taken = ('Main():void =\n    X := trail{}\n    if (Y := X' + chf + '):\n        Print(Y.T)\n'
             '    else:\n        Print("failed")\n')
    s['failable'] = (failable(1000) + taken, wantf)
    s['failable-that-fails'] = (failable(2) + taken, 'failed')
    s['generic-class'] = (EVENT + 'box(t:type) := class:\n    V:t\n    T:string = ""\n'
        + ''.join(decl(m, 'box(t)', new=lambda e: f'box(t){{V := V, T := {e}}}') for m in ALL)
        + main(f'X{ch}.T', '    X := box(float){V := 1.5}\n'), want)
    s['interface'] = (EVENT + 'walk := interface:\n' + ''.join(
            f'    {name}({"N:int" if arg else ""}):walk\n' for name, arg, _ in ALL) + '    Said():string\n'
        + 'trail := class(walk):\n    T:string = ""\n' + ''.join(decl(m, 'walk', ov='<override>',
            new=lambda e: f'trail{{T := {e}}}') for m in ALL)
        + '    Said<override>():string = T\n' + main(f'X{ch}.Said()', '    X:walk = trail{}\n'), want)
    chi, wanti = calls(ALL, n, before='.Inner')
    s['through-a-field'] = (EVENT + 'holder := class:\n    Inner:trail\ntrail := class:\n    T:string = ""\n'
        + ''.join(decl(m, 'holder', new=lambda e: f'holder{{Inner := trail{{T := {e}}}}}') for m in ALL)
        + main(f'X{chi}.Inner.T', '    X := holder{Inner := trail{}}\n'), wanti)
    s['in-a-method-on-Self'] = (EVENT + cls(ALL) + f'    Run():string = Self{ch}.T\n' + main('trail{}.Run()', ''), want)
    s['of-a-type-parameter'] = (EVENT + cls(ALL) + f'Of(X:t where t:subtype(trail)):string = X{ch}.T\n'
        + main('Of(trail{})', ''), want)
    # the program's Signal, then the event's on what the chain gives
    s['then-the-events-own'] = ('Tick():void = Print("tick")\nholder := class:\n    Ev:event()\n    T:string = ""\n'
        + ''.join(decl(m, 'holder', new=lambda e: f'holder{{Ev := Ev, T := {e}}}') for m in [SIGNAL, AWAIT])
        + 'Main():void =\n    E := event(){}\n    S := E.Subscribe(Tick)\n    X := holder{Ev := E}\n'
        + '    X' + calls([SIGNAL, AWAIT], n)[0] + '.Ev.Signal()\n    S.Cancel()\n    X.Signal().Ev.Signal()\n'
        + '    Print(X' + calls([SIGNAL, AWAIT], n)[0] + '.T)\n', 'tick\n' + calls([SIGNAL, AWAIT], n)[1])
    return s
# name: (the program of n calls, its refusal)
def refused(n):
    s = {}
    for m in ALL:
        ch, _ = calls([m], n)
        s[f'no-such-method-after-{m[0].lower()}'] = (EVENT + cls([m]) + main(f'X{ch}.Missing().T'),
                                                     "class trail has no method 'Missing'")
    ch, _ = calls(ALL, n)
    ch3, _ = calls([SIGNAL, CANCEL, AWAIT], n)
    s['unknown-receiver'] = (EVENT + cls(ALL) + main(f'Nowhere{ch}.T', ''), "unknown identifier 'Nowhere'")
    s['argument-too-many'] = (EVENT + cls(ALL) + main(f'X{ch}.Signal(1).T'), 'Signal takes 0 argument(s), found 1')
    s['cannot-fail'] = (EVENT + cls(ALL) + main(f'X{ch}.Await[].T'), 'Await cannot fail: call it with Await(…)')
    s['wrong-type'] = (EVENT + cls(ALL) + 'Main():void =\n    X := trail{}\n    Y:int = X' + ch + '\n',
                       'expected int, found trail')
    s['suspends-outside'] = (cls([SIGNAL, CANCEL, AWAIT], fx='<suspends>', pre='        Sleep(0.0)\n')
                             + main(f'X{ch3}.T'), 'can only be called in a <suspends> function')
    # an event's Await at the end of the chain, where nothing may suspend
    s['then-the-events-own-await'] = ('holder := class:\n    Ev:event()\n    T:string = ""\n'
        + ''.join(decl(m, 'holder', new=lambda e: f'holder{{Ev := Ev, T := {e}}}') for m in [SIGNAL, AWAIT])
        + 'Main():void =\n    X := holder{Ev := event(){}}\n    X' + calls([SIGNAL, AWAIT], n)[0] + '.Ev.Await()\n',
        'Await suspends: it can only be called in a <suspends> function (#156)')
    return s
# An event's and a task's own Await, called on what the Await before it gives
# (#775): an event of events, a task of tasks, n deep. name: (the program, what
# it prints)
def nested(n):
    def of(kind, k, last='int'): return last if k == 0 else f'{kind}({of(kind, k - 1, last)})'
    awaits = '.Await()' * n
    # each level is signalled, after a wait, with the event of the level below
    def senders(last, signal):
        t = f'Send1(E:{of("event", 1, last)})<suspends>:void =\n    Sleep(0.0)\n    {signal}\n'
        for k in range(2, n + 1):
            t += (f'Send{k}(E:{of("event", k, last)})<suspends>:void =\n    Sleep(0.0)\n'
                  f'    I := {of("event", k - 1, last)}{{}}\n    spawn{{Send{k - 1}(I)}}\n    E.Signal(I)\n')
        return t
    def start(last): return f'    E := {of("event", n, last)}{{}}\n    spawn{{Send{n}(E)}}\n'
    s = {}
    s['events'] = (senders('int', 'E.Signal(7)') + 'Main()<suspends>:void =\n' + start('int')
                   + f'    Print("got {{E{awaits}}}")\n', 'got 7')
    # the receiver of the first is a call that prints: it is called once
    s['events-of-a-call'] = (senders('int', 'E.Signal(7)')
        + f'Seen(E:{of("event", n)}):{of("event", n)} =\n    Print("seen")\n    E\n'
        + 'Main()<suspends>:void =\n' + start('int') + f'    Print("got {{Seen(E){awaits}}}")\n', 'seen\ngot 7')
    tasks = 'F0()<suspends>:int =\n    Sleep(0.0)\n    7\n' + ''.join(
        f'F{k}()<suspends>:{of("task", k)} =\n    Sleep(0.0)\n    spawn{{F{k - 1}()}}\n' for k in range(1, n))
    s['tasks'] = (tasks + f'Main()<suspends>:void =\n    T := spawn{{F{n - 1}()}}\n    Print("got {{T{awaits}}}")\n',
                  'got 7')
    s['tasks-of-a-spawn'] = (tasks + f'Main()<suspends>:void =\n    Print("got {{spawn{{F{n - 1}()}}{awaits}}}")\n',
                             'got 7')
    # each is signalled before it is awaited: a sticky event keeps what it was given
    sticky = '    S0 := 7\n' + ''.join(
        f'    S{k} := {of("sticky_event", k)}{{}}\n    S{k}.Signal(S{k - 1})\n' for k in range(1, n + 1))
    s['sticky-events'] = ('Main()<suspends>:void =\n' + sticky + f'    Print("got {{S{n}{awaits}}}")\n', 'got 7')
    # then the Signal(), and the Subscribe, of the event() the chain gives
    unit = 'event()'
    on = 'On():void = Print("on")\n'
    s['events-then-signal'] = (on + senders(unit, 'I := event(){}\n    I.Subscribe(On)\n    E.Signal(I)')
        + 'Main()<suspends>:void =\n' + start(unit) + f'    E{awaits}.Signal()\n    Print("done")\n', 'on\ndone')
    s['events-then-subscribe'] = (on
        + senders(unit, 'I := event(){}\n    E.Signal(I)\n    Sleep(0.0)\n    Print("signals")\n    I.Signal()')
        + 'Main()<suspends>:void =\n' + start(unit) + f'    S := E{awaits}.Subscribe(On)\n    Print("subscribed")\n'
        + '    Sleep(0.0)\n    Sleep(0.0)\n    S.Cancel()\n    Print("done")\n', 'subscribed\nsignals\non\ndone')
    return s
# name: (the program, its refusal)
def nested_refused(n):
    def of(kind, k, last='int'): return last if k == 0 else f'{kind}({of(kind, k - 1, last)})'
    awaits = '.Await()' * n
    s = {}
    for kind in ('event', 'task'):
        use = f'Use(E:{of(kind, n)})'
        s[f'{kind}s-one-too-many'] = (use + f'<suspends>:void =\n    Print("{{E{awaits}.Await()}}")\n',
                                      "int has no method 'Await'")
        s[f'{kind}s-outside-suspends'] = (use + f':void =\n    Print("{{E{awaits}}}")\n',
                                          'can only be called in a <suspends> function')
        # (the type asked for reaches the first receiver, which is refused as it was:
        # it is elaborated at that type, each call's on the way)
        s[f'{kind}s-wrong-type'] = (use + f'<suspends>:void =\n    X:string = E{awaits}\n',
                                    f':2:15: expected {of(kind, n, "string")}, found {of(kind, n)}: {kind} is invariant')
        s[f'{kind}s-unknown-receiver'] = (use + f'<suspends>:void =\n    Print("{{Nowhere{awaits}}}")\n',
                                          "unknown identifier 'Nowhere'")
    return s
for n in (3, 24, 48):
    for name, (program, want) in nested(n).items():
        open(f'{out}/nested-{name}.{n}.verse', 'w').write(program)
        open(f'{out}/nested-{name}.{n}.want', 'w').write(want + '\n')
    for name, (program, refusal) in nested_refused(n).items():
        open(f'{out}/nestedrefused-{name}.{n}.verse', 'w').write(program)
        open(f'{out}/nestedrefused-{name}.{n}.want', 'w').write(refusal + '\n')
for n in (3, 24, 96):
    for name, (program, want) in chains(n).items():
        open(f'{out}/chain-{name}.{n}.verse', 'w').write(program)
        open(f'{out}/chain-{name}.{n}.want', 'w').write(want + '\n')
    for name, (program, refusal) in refused(n).items():
        open(f'{out}/refused-{name}.{n}.verse', 'w').write(program)
        open(f'{out}/refused-{name}.want', 'w').write(refusal + '\n')
PY
chains=0
for short in "$tmp"/chain-*.3.verse; do
  name="$(basename "$short" .3.verse)"
  for n in 3 24 96; do
    status=0
    (cd "$tmp" && ulimit -v 4194304 && timeout "$limit" "$ov" run "$name.$n.verse") \
      >"$tmp/$name.$n.out" 2>"$tmp/$name.$n.err" || status=$?
    if [[ $status != 0 ]] || ! cmp -s "$tmp/$name.$n.want" "$tmp/$name.$n.out"; then
      echo "FAIL concurrency name chains: ${name#chain-} of $n calls, status $status (124: not within ${limit}s)," \
        "wanted '$(head -c 200 "$tmp/$name.$n.want")', got:"
      head -c 400 "$tmp/$name.$n.out" "$tmp/$name.$n.err"; exit 1
    fi
  done
  chains=$((chains + 1))
done
nested=0
for short in "$tmp"/nested-*.3.verse; do
  name="$(basename "$short" .3.verse)"
  for n in 3 24 48; do
    status=0
    (cd "$tmp" && ulimit -v 4194304 && timeout "$limit" "$ov" run "$name.$n.verse" --emit "$tmp/$name.$n.vbc") \
      >"$tmp/$name.$n.out" 2>"$tmp/$name.$n.err" || status=$?
    if [[ $status != 0 ]] || ! cmp -s "$tmp/$name.$n.want" "$tmp/$name.$n.out"; then
      echo "FAIL concurrency name chains: ${name#nested-} $n deep, status $status (124: not within ${limit}s)," \
        "wanted '$(head -c 200 "$tmp/$name.$n.want")', got:"
      head -c 400 "$tmp/$name.$n.out" "$tmp/$name.$n.err"; exit 1
    fi
    # (the C runtime: a receiver elaborated twice left its slots behind, twice
    # as many for each call, and sixteen calls made more than it loads)
    status=0
    timeout "$limit" "$cv" "$tmp/$name.$n.vbc" >"$tmp/$name.$n.cout" 2>"$tmp/$name.$n.cerr" || status=$?
    if [[ $status != 0 ]] || ! cmp -s "$tmp/$name.$n.want" "$tmp/$name.$n.cout"; then
      echo "FAIL concurrency name chains: ${name#nested-} $n deep in the C runtime, status $status, got:"
      head -c 400 "$tmp/$name.$n.cout" "$tmp/$name.$n.cerr"; exit 1
    fi
  done
  nested=$((nested + 1))
done
nestedrefused=0
for short in "$tmp"/nestedrefused-*.3.verse; do
  name="$(basename "$short" .3.verse)"
  for n in 3 24 48; do
    status=0
    (cd "$tmp" && ulimit -v 4194304 && timeout "$limit" "$ov" check "$name.$n.verse") \
      >/dev/null 2>"$tmp/$name.$n.err" || status=$?
    if [[ $status != 4 ]] || ! grep -qF -f "$tmp/$name.$n.want" "$tmp/$name.$n.err"; then
      echo "FAIL concurrency name chains: ${name#nestedrefused-} $n deep, status $status (124: not within" \
        "${limit}s), wanted '$(cat "$tmp/$name.$n.want")', got:"
      head -c 400 "$tmp/$name.$n.err"; exit 1
    fi
  done
  nestedrefused=$((nestedrefused + 1))
done
count=0
for short in "$tmp"/refused-*.3.verse; do
  name="$(basename "$short" .3.verse)"
  # the short chain's refusal, without its place: the chains differ in that only
  (cd "$tmp" && timeout "$limit" "$ov" check "$name.3.verse") >/dev/null 2>"$tmp/$name.3.err" && {
    echo "FAIL concurrency name chains: ${name#refused-} of 3 calls is accepted"; exit 1; }
  sed 's/^[^:]*:[0-9]*:[0-9]*: //' "$tmp/$name.3.err" >"$tmp/$name.3.msg"
  if ! grep -qF -f "$tmp/$name.want" "$tmp/$name.3.msg"; then
    echo "FAIL concurrency name chains: ${name#refused-} of 3 calls, wanted '$(cat "$tmp/$name.want")', got:"
    cat "$tmp/$name.3.err"; exit 1
  fi
  for n in 24 96; do
    status=0
    (cd "$tmp" && ulimit -v 4194304 && timeout "$limit" "$ov" check "$name.$n.verse") \
      >/dev/null 2>"$tmp/$name.$n.err" || status=$?
    sed 's/^[^:]*:[0-9]*:[0-9]*: //' "$tmp/$name.$n.err" >"$tmp/$name.$n.msg"
    if [[ $status != 4 ]] || ! cmp -s "$tmp/$name.3.msg" "$tmp/$name.$n.msg"; then
      echo "FAIL concurrency name chains: ${name#refused-} of $n calls, status $status (124: not within ${limit}s)," \
        "wanted '$(cat "$tmp/$name.3.msg")', got:"
      head -c 400 "$tmp/$name.$n.err"; exit 1
    fi
  done
  count=$((count + 1))
done
echo "concurrency name chains: $chains shapes of chains of 24 and 96 calls that fit, $count shapes refused as at" \
  "3 calls; $nested shapes of an event's and a task's own Await 24 and 48 deep, in both runtimes," \
  "$nestedrefused refused; each within ${limit}s"
