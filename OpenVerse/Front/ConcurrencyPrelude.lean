import OpenVerse.Front.Parser

namespace OpenVerse.Front

/-- The concurrency helpers (#156), written in Verse: the scheduler's
    state (the clock, in ticks of 1/30 s, and the earliest tick a sleeping
    task waits for), and `Sleep`'s frame with its `new`, `init` and `resume`.
    A sleep of `S` seconds wakes at the first tick at or after its deadline,
    the binary64 product `30·S` rounded up, and never sooner than the next
    one (the Book's API reference: "Short sleeps therefore round up").
    `Sleep(0.0)`, as a negative or NaN duration, completes at once without
    suspending (the Book's tested examples in ch. 14: "Completes at once,
    and wins").
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
        else if (F.Secs > 0.0):
            Ticks:float = F.Secs * 30.0
            if (Ticks < 9223372036854775808.0):
                N:int = if (R := Ceil[Ticks]) then (if (R >= 1) then R else 1) else Err()
                set F.Wake = C.Now + N
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
def concPreludeEvents : String :=
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
def concPreludeAwaits : String :=
  let s := concPreludeEvents
  let s := s.replace "    var Ev:logic = false\n" "    var Ev:logic = false\n    var Ends:?event(void) = false\n"
  s.replace "Await(T:task(t) where t:type)<suspends>:t =\n    WaitDone(T)\n    if (R := T.Result?) then R else Err()\n"
    "Await(T:task(t) where t:type)<suspends>:t =\n    if (R := T.Result?) then R else:\n        EvAwait(taskEnds(T))\n        if (V := T.Result?) then V else Err()\ntaskEnds(T:taskBase):event(void) =\n    if (E := T.Ends?) then E else:\n        F := event(void){}\n        set T.Ends = option{F}\n        F\ntaskEnd(T:taskBase):void =\n    if (E := T.Ends?) then signalAll(E, ())\n"

/-- The concurrency prelude's definitions: plain, in event mode (`events`),
    or in await mode (`awaits`, which is event mode too). -/
def concTops (owned : List String := []) (events : Bool := false) (awaits : Bool := false) :
    Except String (List STop) :=
  parsePrelude (if awaits then concPreludeAwaits else if events then concPreludeEvents else concPrelude)
    (owned ++ (if events || awaits then ["CurRoot",
    "WaitRoot", "Pending", "Probe", "Drain", "MainTask", "Ev", "First", "wakeRoot"] else []) ++
    (if awaits then ["Ends", "taskEnds", "taskEnd"] else []) ++ ["sched", "Now", "Next", "sleep", "Pc", "Secs", "Wake", "sleepNew",
    "sleepInit", "sleepResume", "Sleep", "Ticks", "syncMark", "raceMark", "S", "F", "C", "N", "R", "A",
    "Progress", "Roots", "taskBase", "Done", "Result", "waitf", "T", "X", "waitNew", "waitInit", "waitResume",
    "WaitDone", "Await", "spawnMark", "t", "Sch", "Dead", "evrec", "Got", "Next", "Head", "Tail", "Cur", "W", "L", "V",
    "EvAwait", "E", "branchMark", "rushMark", "signalAll", "H", "StickyAwait", "Last", "CancelCur", "Cancelled", "Running", "Root", "CancelReq", "CurTask", "cancelMark"])

end OpenVerse.Front
