# (#724) a function value converted by class variance keeps its effects: a
# <suspends> value waits as the function does (the race goes as with the
# function named), a <transacts><decides> one's failure rolls its writes
# back, and a conversion in a failure context that fails is undone with it.
# Epic's Verse compiler converts such values with no wrapper (UEFN 43.12,
# followup-coerce's value-class-variance); openverse's adapter only calls.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"

WaitThen(A:animal)<suspends>:string =
    Sleep(1.0)
    A.Name()
RunSuspends(F(:dog)<suspends>:string)<suspends>:string = F(dog{})
Slow()<suspends>:string =
    Sleep(2.0)
    "slow"

store := class:
    var Seen:int = 0
    Note(A:animal)<transacts><decides>:int =
        set Seen += 1
        Seen > 1
        Seen
RunNote(F(:dog)<transacts><decides>:int):int =
    if (X := F[dog{}]) then X else -1

Main()<suspends>:void =
    W:type{_(:animal)<suspends>:string} = WaitThen
    Winner := race:
        RunSuspends(W)
        Slow()
    Print("race {Winner}")
    Print("named {RunSuspends(WaitThen)}")
    S := store{}
    N:type{_(:animal)<transacts><decides>:int} = S.Note
    # the first call fails, its write rolled back; the second succeeds
    Print("{RunNote(N)} {S.Seen}")
    set S.Seen = 1
    Print("{RunNote(N)} {S.Seen}")
    if (G:type{_(:dog)<transacts><decides>:int} = N, G[dog{}] > 10):
        Print("unreachable")
    Print("after {S.Seen}")
    Ns:[]type{_(:dog)<transacts><decides>:int} = array{N, N}
    for (F : Ns, X := F[dog{}]) { Print("{X}") }
