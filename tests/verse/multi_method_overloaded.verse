# Overloaded methods with several values (#283): each list of an overloaded method is a method of
# its own, and a call takes the list its arguments fit, picked by an elaboration before the one that
# inlines it (as the family of a use is). A class with a list of several values and an ordinary one;
# calls through a receiver, bare and through Self in the class; through a base-typed receiver of a
# subclass that overrides both, the string list not; (super:) of the list with several values; an
# array of both classes; first success; and a subclass that adds a list of its own
a := class:
    K : int = 3
    Vals()<transacts>:int = K | K * 10
    Vals(X : int)<transacts>:int = X + K
    Run()<transacts>:void =
        for (X := Vals()) { Print("bare {X}") }
        for (X := Self.Vals()) { Print("self {X}") }
        Print("one {Vals(5)}")
base := class:
    K : int = 1
    Vals()<transacts>:int = K | K * 10
    Vals(X : int)<transacts>:int = X + K
    Vals(S : string)<transacts>:int = S.Length | 100
sub := class(base):
    Vals<override>()<transacts>:int = K + 1 | K + 2 | (super:)Vals()
    Vals<override>(X : int)<transacts>:int = X * 2
    Run()<transacts>:void =
        for (X := Vals()) { Print("sub bare {X}") }
        Print("sub one {Vals(7)}")
        for (X := Vals("ab")) { Print("sub str {X}") }
top := class:
    Get()<transacts>:int = 1 | 2
below := class(top):
    Get(X : int)<transacts>:int = X | X + 1
Main()<transacts>:void =
    A := a{}
    for (X := A.Vals()) { Print("recv {X}") }
    Print("plain {A.Vals(1)}")
    A.Run()
    B : base = sub{K := 5}
    for (X := B.Vals()) { Print("b {X}") }
    Print("b one {B.Vals(3)}")
    for (X := B.Vals("q")) { Print("b str {X}") }
    S := sub{K := 2}
    S.Run()
    if (X := B.Vals(), X > 6) then Print("first {X}")
    Bs : []base = array{base{}, sub{}}
    for (O : Bs, X := O.Vals()) { Print("all {X}") }
    T : top = below{}
    for (X := T.Get()) { Print("top {X}") }
    U := below{}
    for (X := U.Get(), Y := U.Get(X * 10)) { Print("below {X} {Y}") }
