# (#515, --default-no-rollback) what Epic's default effect, no_rollback,
# still admits: a function without specifiers called outside every failure
# context, <transacts> and <computes> functions in conditions, a class's
# block: calling a <transacts> function (Book of Verse tests,
# Effects.versetest:550), a <transacts> function where a function type
# without specifiers is expected (fewer effects), a value of that type
# called outside failure contexts, and a <decides> function without a heap
# specifier, whose no_rollback the evidence leaves open, neither of whose
# calls is judged
Log(N:int):void = Print("log {N}")
Twice(N:int)<transacts>:int = N * 2
Small(N:int)<computes>:logic = if (N < 3) then true else false
Positive(N:int)<decides>:void =
    Log(N)
    N > 0
Apply(F:int->int, N:int):int = F(N)
counter := class:
    var N:int = 0
    block:
        set N = Twice(5)
Main():void =
    Log(1)
    if (Twice(2) = 4) then Print("twice")
    for (I := 0..5, Small(I)?) { Print("small {I}") }
    Print("counter {counter{}.N}")
    Print("applied {Apply(Twice, 7)}")
    if (Positive[3]) then Print("positive")
