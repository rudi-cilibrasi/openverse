import OpenVerse.Front.Parser

namespace OpenVerse.Front

/-- The concurrency helpers (#156), written in Verse: the scheduler's
    state (the clock, in ticks of 1/30 s, and the earliest tick a sleeping
    task waits for), and `Sleep`'s frame with its `new`, `init` and `resume`.
    A sleep of `S` seconds wakes at the first tick at or after its deadline,
    the binary64 product `30·S` rounded up, and never sooner than the next
    one (the Book's API reference: "Short sleeps therefore round up").
    `Sleep(0.0)` waits one tick, as any positive duration below a tick
    does: it yields, and resumes on the next update (Epic's Verse VM and
    Blueprint VM, UEFN 43.12; the Book's API reference: "0.0 resumes on
    the next update and, crucially, does yield"). A negative or NaN
    duration completes at once without suspending.
    `Sleep` itself is a stub that only marks the suspension point: the
    lowering (`Suspend.lean`) calls the others in its place. -/
def concPrelude : String := "
sched := class:
    var Now:int = 0
    var Next:int = -1
    var Progress:logic = false
    var Head:?int = false
    var Tail:?int = false
    var Dead:logic = false
    var CancelCur:logic = false
    var CurTask:taskBase = taskBase{}
taskBase := class:
    var Done:logic = false
    var Sch:?sched = false
    var Cancelled:logic = false
    var Running:logic = false
    var Root:?int = false
    var CancelReq:logic = false
task(t:type) := class(taskBase):
    var Result:?t = false
waitf := class:
    var Pc:int = 0
    var T:taskBase
waitNew(X:taskBase):waitf = waitf{T := X}
waitInit(F:waitf, X:taskBase):void =
    set F.Pc = 0
    set F.T = X
waitResume(F:waitf, C:sched):int =
    if (F.T.Cancelled?):
        set C.CancelCur = true
        return 0
    if (F.T.Done?) then return 1
    if (F.Pc = 0):
        set F.Pc = 1
        set F.T.Sch = option{C}
    0
WaitDone(X:taskBase)<suspends><computes>:void = {}
Await(T:task(t) where t:type)<suspends>:t =
    WaitDone(T)
    if (R := T.Result?) then R else Err()
spawnMark(A:[]void)<computes>:void = {}
cancelMark(X:taskBase)<suspends><computes>:void = {}
branchMark(A:[]void)<computes>:void = {}
evrec(t:type) := class(taskBase):
    var Got:?t = false
    var Next:?evrec(t) = false
event(t:type) := class:
    var Head:?evrec(t) = false
    var Tail:?evrec(t) = false
    Signal(X:t):void =
        if (Head?) then signalAll(Self, X)
signalAll(E:event(t), X:t where t:type):void =
    var Cur:?evrec(t) = E.Head
    set E.Head = false
    set E.Tail = false
    loop:
        if (W := Cur?):
            set W.Got = option{X}
            set W.Done = true
            if (S := W.Sch?) then set S.Progress = true
            set Cur = W.Next
        else:
            break
EvAwait(E:event(t) where t:type)<suspends>:t =
    loop:
        if (H := E.Head?, H.Done?):
            set E.Head = H.Next
        else:
            break
    if (E.Head?) {} else { set E.Tail = false }
    W := evrec(t){}
    if (L := E.Tail?) then set L.Next = option{W} else set E.Head = option{W}
    set E.Tail = option{W}
    defer:
        set W.Done = true
    WaitDone(W)
    if (V := W.Got?) then V else Err()
sticky_event(t:type) := class(event(t)):
    var Last:?t = false
    Signal<override>(X:t):void =
        set Last = option{X}
        if (Head?) then signalAll(Self, X)
StickyAwait(E:sticky_event(t) where t:type)<suspends>:t =
    if (V := E.Last?) then V else EvAwait(E)
sleep := class:
    var Pc:int = 0
    var Secs:float = 0.0
    var Wake:int = 0
sleepNew(S:float):sleep = sleep{Secs := S}
sleepInit(F:sleep, S:float):void =
    set F.Pc = 0
    set F.Secs = S
sleepResume(F:sleep, C:sched):int =
    if (F.Pc = 0):
        set F.Pc = 1
        if (F.Secs = 1.0 / 0.0):
            set F.Wake = -1
        else if (F.Secs >= 0.0):
            Ticks:float = F.Secs * 30.0
            if (Ticks < 9223372036854775808.0):
                N:int = if (R := Ceil[Ticks]) then (if (R >= 1) then R else 1) else Err()
                At:int = C.Now + N
                # (the reference clock counts ticks in 64 bits, #514: ints go
                # past them, #724, so a wake past them is the overflow error
                # that ToString raises for an int beyond 64 bits)
                ToString(At)
                set F.Wake = At
            else:
                Err()
        else:
            return 1
    if (F.Wake < 0):
        return 0
    if (C.Now >= F.Wake):
        return 1
    if (C.Next < 0):
        set C.Next = F.Wake
    else if (F.Wake < C.Next):
        set C.Next = F.Wake
    0
Sleep(S:float)<suspends><computes>:void = {}
syncMark(A:[]void)<suspends><computes>:void = {}
raceMark(A:[]void)<suspends><computes>:void = {}
rushMark(A:[]void)<suspends><computes>:void = {}
"

set_option compiler.extract_closed false in
/-- `concPrelude` in event mode (a program that uses an event type): the
    Book's rule that a `Signal` resumes its awaiters inside it, in the
    order they suspended, each until it waits again or ends (the Book's
    API, `event`'s `Signal`; docs/research/scheduler-conformance.md,
    "Awaiters run inside `Signal`"). The scheduler keeps the root running
    (`CurRoot`, which `$Run`, the `start` functions and `$wakeRoot` set
    around a root's run), a probe flag (a `rush` loser's one poll as a root
    of its own), the depth of the `Signal`s running (`Drain`) and `Main`'s
    task. A waiter records the root it waits in at each poll (`WaitRoot`, a
    statement the lowering adds), is pending from its `Signal` until its
    turn, and an event's (`Ev`) is told from a task's. `signalAll` takes
    the event's round, marks each awaiter in it, then resumes each, in
    order, through `$wakeRoot`, whose body the lowering gives (a dispatch
    on the root's class). Inside a `Signal`, only an event awaiter's turn
    goes on: a sleep that expired and a task wait report waiting and ask
    for another pass. The two root fields are typed `?int` here and patched
    to the roots' type in the class table by the lowering; the prelude's
    code never reads them. -/
def concPreludeEvents : Thunk String := Thunk.mk fun _ =>
  let s := concPrelude
  let s := s.replace "    var CurTask:taskBase = taskBase{}\n"
    "    var CurTask:taskBase = taskBase{}\n    var CurRoot:?int = false\n    var Probe:logic = false\n    var Drain:int = 0\n    var MainTask:taskBase = taskBase{}\n"
  let s := s.replace "    var CancelReq:logic = false\n"
    "    var CancelReq:logic = false\n    var WaitRoot:?int = false\n    var Pending:logic = false\n    var Ev:logic = false\n"
  let s := s.replace "waitResume(F:waitf, C:sched):int =\n    if (F.T.Cancelled?):\n        set C.CancelCur = true\n        return 0\n    if (F.T.Done?) then return 1\n    if (F.Pc = 0):\n        set F.Pc = 1\n        set F.T.Sch = option{C}\n    0\n" "waitResume(F:waitf, C:sched):int =\n    if (C.Probe?) then return 0\n    if (F.Pc = 0):\n        set F.Pc = 1\n        set F.T.Sch = option{C}\n    else if (C.Drain > 0, not F.T.Ev?):\n        if (F.T.Done? or F.T.Cancelled?) then set C.Progress = true\n        return 0\n    if (F.T.Cancelled?):\n        set C.CancelCur = true\n        return 0\n    if (F.T.Done?, not F.T.Pending?) then return 1\n    0\n"
  let s := s.replace "signalAll(E:event(t), X:t where t:type):void =\n    var Cur:?evrec(t) = E.Head\n    set E.Head = false\n    set E.Tail = false\n    loop:\n        if (W := Cur?):\n            set W.Got = option{X}\n            set W.Done = true\n            if (S := W.Sch?) then set S.Progress = true\n            set Cur = W.Next\n        else:\n            break\n" "signalAll(E:event(t), X:t where t:type):void =\n    var Cur:?evrec(t) = E.Head\n    set E.Head = false\n    set E.Tail = false\n    First:?evrec(t) = Cur\n    loop:\n        if (W := Cur?):\n            if (not W.Done?):\n                set W.Got = option{X}\n                set W.Done = true\n                set W.Pending = true\n            set Cur = W.Next\n        else:\n            break\n    set Cur = First\n    loop:\n        if (W := Cur?):\n            if (W.Pending?):\n                set W.Pending = false\n                if (S := W.Sch?):\n                    set S.Drain += 1\n                    wakeRoot(W, S)\n                    set S.Drain -= 1\n            set Cur = W.Next\n        else:\n            break\nwakeRoot(W:taskBase, S:sched):void = {}\n"
  let s := s.replace "    W := evrec(t){}\n" "    W := evrec(t){Ev := true}\n"
  let s := s.replace "    defer:\n        set W.Done = true\n    WaitDone(W)\n"
    "    defer:\n        set W.Done = true\n        set W.Pending = false\n    WaitDone(W)\n"
  let s := s.replace "sleepResume(F:sleep, C:sched):int =\n" "sleepResume(F:sleep, C:sched):int =\n    if (C.Probe?) then return 0\n"
  s.replace "    if (C.Now >= F.Wake):\n        return 1\n"
    "    if (C.Now >= F.Wake):\n        if (C.Drain > 0):\n            set C.Progress = true\n            return 0\n        return 1\n"

set_option compiler.extract_closed false in
/-- `concPreludeEvents` in await mode (a program that awaits a task): the
    Book's rule that a task's end resumes its awaiters inside it, in the
    order they registered, each until it waits again or ends (the Book's
    API, `task`'s `Await`; docs/research/scheduler-conformance.md, "A
    task's end resumes its awaiters"). A task's end is a `Signal` of an
    event of its own, `Ends`, which its first awaiter makes: `Await` gives
    the result of a task that has one at once, and otherwise awaits the end
    event, then gives the result; `taskEnd`, which a spawned call's root
    calls once it has set its task's result, signals it. A cancelled task
    never sets a result nor signals its end, so its awaiters wait for ever.
    The field is `taskBase`'s, so that `taskEnd`, which the lowering's code
    calls, is not generic. -/
def concPreludeAwaits : Thunk String := Thunk.mk fun _ =>
  let s := concPreludeEvents.get
  let s := s.replace "    var Ev:logic = false\n" "    var Ev:logic = false\n    var Ends:?event(void) = false\n"
  s.replace "Await(T:task(t) where t:type)<suspends>:t =\n    WaitDone(T)\n    if (R := T.Result?) then R else Err()\n"
    "Await(T:task(t) where t:type)<suspends>:t =\n    if (R := T.Result?) then R else:\n        EvAwait(taskEnds(T))\n        if (V := T.Result?) then V else Err()\ntaskEnds(T:taskBase):event(void) =\n    if (E := T.Ends?) then E else:\n        F := event(void){}\n        set T.Ends = option{F}\n        F\ntaskEnd(T:taskBase):void =\n    if (E := T.Ends?) then signalAll(E, ())\n"

/-- `prelude` with scopes (#724), for a program with a `branch` or a `rush`:
    a task's children (its branches, the arms of its `rush`es that go on)
    are stopped when the task ends, as on Epic's Verse VM ("Tasks are
    cancelled when their PARENT TASK ends", the Book's
    `Tests/Bugs/BPVMOnly/AsyncContextCancellation.versetest`), not when the
    function that started them returns. A scope is a list of children (the
    lowering's root cells; `Own`: not the class's prototype, which is
    `Main`'s scope); the scheduler holds the scope whose code runs and
    `Main`'s, a task its own. The lowering does the rest (`$stopScope`). -/
def withScopes (prelude : String) : String :=
  -- (the scheduler's fields after its others, which the lowering reaches
  -- by their places; `Unwinding`, the scope of the task being cancelled
  -- whose children are still to be stopped, before its first defer runs:
  -- `OuterUnwind` the one it hides, `UnwindDue` whether still to stop)
  let s := prelude.replace "taskBase := class:\n"
    "    var Scope:scope = scope{}\n    var MainScope:scope = scope{}\n    var Unwinding:?scope = false\nscope := class:\n    var Kids:?int = false\n    var Own:logic = false\n    var OuterUnwind:?scope = false\n    var UnwindDue:logic = false\ntaskBase := class:\n"
  let s := s.replace "    var Result:?t = false\n" "    var Result:?t = false\n    var TScope:scope = scope{}\n"
  -- (await mode: a task whose call has ended has its result before its
  -- children are stopped, and is done after: an `Await` made meanwhile, in
  -- a child's defer, waits for it to be done, with the other awaiters)
  s.replace "Await(T:task(t) where t:type)<suspends>:t =\n    if (R := T.Result?) then R else:\n"
    "Await(T:task(t) where t:type)<suspends>:t =\n    if (T.Done?, R := T.Result?) then R else:\n"

/-- `concPrelude` (in any mode) with subscriptions (#210, #724): Epic's
    `event(t)` has `Subscribe` (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
    Verse VM: tests/conformance/versevm/followup/subscribe-in-transacts.verse),
    so an event keeps the functions subscribed to it, each with its
    subscription (`subPrelude`'s `subscription`, a `cancelable`), and its
    `Signal`, a sticky event's too, first resumes the awaiters (the Book's
    API: "Subscribers ... are invoked only after every waiting task has
    been resumed"), then calls the functions subscribed at that point, in
    the order they subscribed, each skipped if cancelled before its turn,
    and drops the cancelled ones. So a function that a resumed awaiter
    subscribes is called by that `Signal`, and one that a called function
    subscribes is not, as on Epic's Verse VM (UEFN 43.12, 2026-11-19:
    followup-event/subscribe-from-awaiter, subscribe-during-signal; the
    VM's order of the functions varies, followup-event/subscribe-order).
    `Subscribe` adds one. -/
def withSubscriptions (s : String) : String :=
  let notify := "        Hs := Handlers\n        set Handlers = for (H : Hs, H(0).Live?) { H }\n" ++
    "        for (H : Hs, H(0).Live?):\n            H(1)(X)\n"
  let s := s.replace
    "    var Tail:?evrec(t) = false\n    Signal(X:t):void =\n        if (Head?) then signalAll(Self, X)\n"
    ("    var Tail:?evrec(t) = false\n    var Handlers:[]tuple(subscription, type{_(:t):void}) = array{}\n" ++
     "    Signal(X:t):void =\n        if (Head?) then signalAll(Self, X)\n" ++ notify ++
     "    Subscribe(F:type{_(:t):void}):cancelable =\n        S := subscription{}\n" ++
     "        set Handlers += array{(S, F)}\n        S\n")
  s.replace "        set Last = option{X}\n        if (Head?) then signalAll(Self, X)\n"
    ("        set Last = option{X}\n        if (Head?) then signalAll(Self, X)\n" ++ notify)

/-- The concurrency prelude's definitions: plain, in event mode (`events`),
    or in await mode (`awaits`, which is event mode too), with scopes
    (`scopes`, #724) for a program with a `branch` or a `rush`. Add the
    public signaling interface when a source type needs it, and
    subscriptions (`withSubscriptions`, with `subTops`) when the program
    subscribes. -/
def concTops (owned : List String := []) (events : Bool := false) (awaits : Bool := false)
    (usesSignalable : Bool := false) (subscribes : Bool := false) (scopes : Bool := false) :
    Except String (List STop) := do
  let prelude := if awaits then concPreludeAwaits.get else if events then concPreludeEvents.get else concPrelude
  let prelude := if scopes then withScopes prelude else prelude
  let prelude := if subscribes then withSubscriptions prelude else prelude
  -- (both `Signal`s, the event's and the sticky event's, call the functions)
  if subscribes && (prelude.splitOn "            H(1)(X)\n").length != 3 then
    throw "internal: the concurrency prelude's events did not take subscriptions (#724)"
  let prelude := if usesSignalable then
    prelude.replace "event(t:type) := class:\n" ("signalable(t:type) := interface:\n" ++
      "    Signal(X:t):void\nevent(t:type) := class(signalable(t)):\n") |>.replace
      "    Signal(X:t):void =\n" "    Signal<override>(X:t):void =\n"
    else prelude
  parsePrelude prelude
    (owned ++ (if events || awaits then ["CurRoot",
    "WaitRoot", "Pending", "Probe", "Drain", "MainTask", "Ev", "First", "wakeRoot"] else []) ++
    (if awaits then ["Ends", "taskEnds", "taskEnd"] else []) ++
    (if scopes then ["scope", "Kids", "Own", "Scope", "MainScope", "TScope", "Unwinding", "OuterUnwind",
      "UnwindDue"] else []) ++ ["sched", "Now", "Next", "sleep", "Pc", "Secs", "Wake", "sleepNew",
    "sleepInit", "sleepResume", "Sleep", "Ticks", "syncMark", "raceMark", "S", "F", "C", "N", "R", "A",
    "Progress", "Roots", "taskBase", "Done", "Result", "waitf", "T", "X", "waitNew", "waitInit", "waitResume",
    "WaitDone", "Await", "spawnMark", "t", "Sch", "Dead", "evrec", "Got", "Next", "Head", "Tail", "Cur", "W", "L", "V",
    "EvAwait", "E", "branchMark", "rushMark", "signalAll", "H", "StickyAwait", "Last", "CancelCur", "Cancelled", "Running", "Root", "CancelReq", "CurTask", "cancelMark"] ++
    (if subscribes then ["subscription", "Live", "Handlers", "Hs"] else []))

end OpenVerse.Front
