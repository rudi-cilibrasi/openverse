# expect: 12:37: this call may signal an event (Tell → event.Signal) in a failure context, which the no_rollback effect of an event's Signal does not allow
# (#515, #283) a Signal in a clause of a condition
# with a choice, whose branch breaks: alternatives that fail are rolled back
# (the break is the branch's: it cannot leave the condition, a failure
# context, the Book of Verse's tests, SOL-4199-BreakFromIf.versetest:4)
Tell(E:event(int), V:int):int =
    E.Signal(V)
    V
Main()<suspends>:void =
    E := event(int){}
    loop:
        if (X := 1 | 2 | 3, Y := Tell(E, X), Y > 1) then break
        break
