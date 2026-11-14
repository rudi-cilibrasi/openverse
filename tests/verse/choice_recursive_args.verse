# Recursive functions with several values (#235): arguments that fail,
# choices and calls in arguments, the declared result type, indexing, and a
# pure function value.
CPos(X:int)<computes><decides>:int =
    X > 0
    X
# (the second alternative's argument fails: it alone gives no value)
Down(N:int, A:int)<computes><decides>:int =
    N >= 0
    A | Down[N - 1, CPos[A - 1]]
Two(X:int)<computes>:int = X | X - 10
# (a call with several values in a recursive call's argument)
Chain(N:int)<computes><decides>:int =
    N >= 0
    N | Chain[Two(N) - 1]
Count(N:int)<computes><decides>:int =
    N >= 0
    N | Count[N - 1]
# (the result type reaches the last expression's alternatives)
Opt(N:int)<computes><decides>:?int =
    N >= 0
    false | option{N} | Opt[N - 1]
Empty(N:int)<computes><decides>:[]int =
    N > 0
    array{} | Empty[N - 1]
animal := class<computes>:
    Name():string = "animal"
dog := class<computes>(animal):
    Name<override>():string = "dog"
cat := class<computes>(animal):
    Name<override>():string = "cat"
Pets(N:int)<computes><decides>:animal =
    N > 0
    dog{} | cat{} | Pets[N - 1]
# (indexing a parameter is no call through a function value)
First(A:[]int, N:int)<computes><decides>:int =
    N > 0
    A[0] | First[A, N - 1]
Second(A:tuple(int, int), N:int)<computes><decides>:int =
    N > 0
    A(1) | Second[A, N - 1]
Double(N:int)<computes>:int = 2 * N
Apply(Op:type{_(:int)<computes>:int}, N:int)<computes><decides>:int =
    N > 0
    Op(N) | Apply[Op, N - 1]
Main():void =
    for (X := Down[1, 1]) { Print("down {X}") }
    for (X := Chain[1]) { Print("chain {X}") }
    for (X := Count[1 | 2]) { Print("choice arg {X}") }
    for (X := Count[Count[1]]) { Print("nested {X}") }
    for (X := Opt[1]) { Print("opt {X? or -1}") }
    for (X := Empty[2]) { Print("empty {X.Length}") }
    for (P := Pets[2]) { Print(P.Name()) }
    for (X := First[array{9}, 2]) { Print("first {X}") }
    for (X := Second[(3, 4), 2]) { Print("second {X}") }
    for (X := Apply[Double, 3]) { Print("apply {X}") }
    # (an argument that fails is a clause: the clauses before it roll back)
    var N:int = 0
    for ((set N = 2; true?), X := Count[array{1}[5]]) { Print("never") }
    Print("n {N}")
    if (set N = 3, X := Count[array{1}[5]]) then Print("never") else Print("n {N}")
