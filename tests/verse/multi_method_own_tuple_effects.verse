# Computed super tuples bind their own types; every operand runs once.
base := class:
    Emit(X:t,Y:[]t,?Z:?t=false where t:type)<transacts><decides>:t =
        Print("base {Y.Length}")
        X|Z?
child := class(base):
    Emit<override>(X:u,Y:[]u,?Z:?u=false where u:type)<transacts><decides>:u =
        Print("child")
        X|(super:)Emit[Args(X)]
Args(X:v where v:type)<transacts>:tuple(v,[]v) =
    Print("tuple")
    (X,array{})
Make()<transacts>:child =
    Print("receiver")
    child{}
Main():void =
    for(V:=Make().Emit[Args("s")]): Print("all {V}")
    if(V:=Make().Emit[Args("p")],V="p")then Print("first {V}")
    if(V:=Make().Emit[Args("r")],V="q")then Print("unexpected")else Print("none")
