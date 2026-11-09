# Review of overridden methods with several values (#283): arguments at
# their parameters' types (array{}, map{}, false), one tuple argument to
# several parameters with a single-valued implementation, and the eager
# route (F$all) with the dispatch in a nested for; a return type spelled
# two ways (string, []char); function types whose effects are written in
# another order; an abstract override below the only implementation;
# (super:) with one tuple argument
shape := class:
    Count(Xs : []int, M : [int]int, O : ?int)<transacts>:int = Xs.Length + M.Length | (if (V := O?) then V else 7)
    Add2(A : int, B : int)<transacts>:int = A + B | A * B
    Sizes()<computes>:int = 1 | 2
big := class(shape):
    Count<override>(Xs : []int, M : [int]int, O : ?int)<transacts>:int = 100
    Add2<override>(A : int, B : int)<transacts>:int = 1000
    Sizes<override>()<computes>:int = 7
parentc := class:
    Text()<transacts>:string = "a" | "b"
childc := class(parentc):
    Text<override>()<transacts>:[]char = "c"
Inc(X:int)<decides><transacts>:int = X + 1
Dec(X:int)<decides><transacts>:int = X - 1
fns := class:
    Fs()<transacts>:type{_(:int)<decides><transacts>:int} = Inc | Dec
bigf := class(fns):
    Fs<override>()<transacts>:type{_(:int)<transacts><decides>:int} = Dec
onlyc := class:
    Sz()<transacts>:int = 1 | 2
midc := class<abstract>(onlyc):
    Sz<override>()<transacts>:int
lowc := class(midc):
    K : int = 0
pair := class:
    Sum2(A : int, B : int)<transacts>:int = A + B | A * B
bigp := class(pair):
    Sum2<override>(A : int, B : int)<transacts>:int =
        T := (A, B + 1)
        (super:)Sum2(T)
Walk(O : shape, N : int)<computes>:int =
    A := for (X := O.Sizes()) { X }
    if (N > 0) then (N | Walk(O, N - 1)) else A.Length
Main()<transacts>:void =
    for (X := shape{}.Count(array{}, map{}, false)):
        Print("c {X}")
    for (X := big{}.Count(array{}, map{}, false)):
        Print("b {X}")
    T := (3, 4)
    for (X := shape{}.Add2(T)):
        Print("t {X}")
    for (X := big{}.Add2(T)):
        Print("u {X}")
    for (V := Walk(shape{}, 1)):
        Print("w {V}")
    for (V := Walk(big{}, 1)):
        Print("v {V}")
    # (the same return type spelled two ways: string is []char)
    for (S := childc{}.Text()):
        Print(S)
    for (S := parentc{}.Text()):
        Print(S)
    F0 : fns = bigf{}
    for (F := F0.Fs(), Y := F[10]):
        Print("f {Y}")
    Os : []onlyc = array{onlyc{}, lowc{}}
    for (O : Os, X := O.Sz()):
        Print("o {X}")
    for (V := bigp{}.Sum2(2, 3)):
        Print("p {V}")
