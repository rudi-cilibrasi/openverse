import OpenVerse.Front.Parser

namespace OpenVerse.Front

/-- The concurrency helpers (#156), written in Verse: the scheduler's
    state (the clock, in ticks of 1/30 s, and the earliest tick a sleeping
    task waits for), and `Sleep`'s frame with its `new`, `init` and `resume`.
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
                N:int = if (R := Round[Ticks]) then (if (R >= 1) then R else 1) else Err()
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

/-- (#513) `concPrelude` for FIFO event resumption: the scheduler keeps the
    root running (`CurRoot`) and a list of the waiters `Signal` woke, in
    its order (`WokenHead`, `WokenTail`, each task's `WokenNext`); a waiter
    records the root it waits in (`WaitRoot`). The lowering patches the two
    root fields' types to its roots' and runs the woken ones' roots in that
    order (`lowerConcurrency`); the prelude's code never reads them. -/
def concPreludeFifo : String :=
  let s := concPrelude
  let s := s.replace "    var CurTask:taskBase = taskBase{}\n"
    "    var CurTask:taskBase = taskBase{}\n    var CurRoot:?int = false\n    var WokenHead:?taskBase = false\n    var WokenTail:?taskBase = false\n    var Probe:logic = false\n"
  let s := s.replace "    var CancelReq:logic = false\n"
    "    var CancelReq:logic = false\n    var WaitRoot:?int = false\n    var WokenNext:?taskBase = false\n    var Pending:logic = false\n"
  -- (only a waiter this `Signal` wakes: a record already done, of a wait
  -- that was cancelled, which its `defer:` marked, is no waiter)
  let s := s.replace "            set W.Got = option{X}\n            set W.Done = true\n            if (S := W.Sch?) then set S.Progress = true\n"
    "            WasDone := W.Done\n            set W.Got = option{X}\n            set W.Done = true\n            if (S := W.Sch?):\n                set S.Progress = true\n                if (not WasDone?):\n                    set W.Pending = true\n                    set W.WokenNext = false\n                    if (WT := S.WokenTail?) then set WT.WokenNext = option{W} else set S.WokenHead = option{W}\n                    set S.WokenTail = option{W}\n"
  -- (a woken waiter goes on only at its turn, when the drain unmarks it: a
  -- task resumed for another's turn, an arm's sibling, leaves it waiting)
  let s := s.replace "    if (F.T.Done?) then return 1\n" "    if (F.T.Done?, not F.T.Pending?) then return 1\n"
  -- (a probe, `Probe`: a poll that only records the root each waiter waits
  -- in, and goes on nowhere, for a `rush` loser that becomes a task)
  let s := s.replace "waitResume(F:waitf, C:sched):int =\n" "waitResume(F:waitf, C:sched):int =\n    if (C.Probe?) then return 0\n"
  s.replace "sleepResume(F:sleep, C:sched):int =\n" "sleepResume(F:sleep, C:sched):int =\n    if (C.Probe?) then return 0\n"

def concTops (owned : List String := []) (fifo : Bool := false) : Except String (List STop) :=
  parsePrelude (if fifo then concPreludeFifo else concPrelude) (owned ++ (if fifo then ["CurRoot", "WokenHead",
    "WokenTail", "WaitRoot", "WokenNext", "WT", "WasDone", "Pending", "Probe"] else []) ++ ["sched", "Now", "Next", "sleep", "Pc", "Secs", "Wake", "sleepNew",
    "sleepInit", "sleepResume", "Sleep", "Round", "Ticks", "syncMark", "raceMark", "S", "F", "C", "N", "R", "A",
    "Progress", "Roots", "taskBase", "Done", "Result", "waitf", "T", "X", "waitNew", "waitInit", "waitResume",
    "WaitDone", "Await", "spawnMark", "t", "Sch", "Dead", "evrec", "Got", "Next", "Head", "Tail", "Cur", "W", "L", "V",
    "EvAwait", "E", "branchMark", "rushMark", "signalAll", "H", "StickyAwait", "Last", "CancelCur", "Cancelled", "Running", "Root", "CancelReq", "CurTask", "cancelMark"])

end OpenVerse.Front
