# An if with a cast that refines type arguments among its clauses (#243)
# takes the type any if takes with no expected type (#32, #366): a void
# branch makes it void, branches with nothing in common give `any`, and
# `false` against an else's option is its empty one. Its branch is typed
# under the refinement, alone, with clauses after the cast (#286), before
# it (#400), or with var copy-outs and returns (refineExits).
box(t:type) := class:
    V:t
ibox := class(box(int)):
    W:int = 2
animal := class:
    N:int = 1
dog := class(animal):
    D:int = 2
Statements(B:box(t), Z:logic where t:type):int =
    var N:int = 0
    if (I := ibox[B]) then Print("only {I.W}") else "x"
    if (I := ibox[B], I.W > 0) then Print("first {I.W}") else "x"
    if (Z?, I := ibox[B]) then Print("later {I.W}") else "x"
    if (I := ibox[B]) then { set N += I.W; Print("set {N}") } else "x"
    if (I := ibox[B]) then { if (I.W > 5) then return 0; Print("ret {I.W}") } else "x"
    if (I := ibox[B]) then I.W + 1 else "x"
    if (Z?, I := ibox[B]) then I.W + 1 else "x"
    N
Values(B:box(t), Z:logic where t:type):void =
    O := if (I := ibox[B]) then (Print("o{I.W}"); false) else option{1}
    P := if (I := ibox[B], I.W > 0) then (Print("p{I.W}"); false) else option{2}
    Q := if (Z?, I := ibox[B]) then (Print("q{I.W}"); false) else option{3}
    A := if (I := ibox[B]) then dog{D := I.W} else animal{}
    S := if (Z?, I := ibox[B]) then "s{I.W}" else "e"
    Print("{O? or 9} {P? or 9} {Q? or 9} {A.N} {S}")
Main():void =
    Print("{Statements(ibox{V := 1}, true)}")
    Print("{Statements(box(string){V := "a"}, false)}")
    Values(ibox{V := 1}, true)
    Values(box(string){V := "a"}, false)
