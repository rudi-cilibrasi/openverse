# (#724) --function-coercions keeps openverse's conversions of function values
# that Epic's Verse compiler refuses with error 3502: a branch of an if of
# another function type, a higher-order generic function as a value, a call
# of a generic function or a parametric class's method whose result has a
# type parameter inside a function type, an override of a parametric
# interface's method with one, and a function value that is no name (a
# parameter, an option's content) at another function type.
F2(?A:int = 2):int = A
F4(?B:int = 4):int = B
Identity(X:t where t:type)<computes>:t = X
DecidesIdentity(X:t where t:type)<computes><decides>:t = X
One(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(X)
Succ(X:int)<transacts>:int = X + 1
Twice(A(F(:int)<transacts>:int, X:int)<transacts>:int)<transacts>:int = A(Succ, A(Succ, 0))
TakeInt(X:int):void = Print("took {X}")
TakeT(X:int)<transacts>:void = Print("took {X}")
Wrap(X:t, F(:t):void where t:type):(t->void) = F
a(t:type) := interface:
    F(G(:t)<transacts>:void)<transacts>:void
b := class(a(int)):
    F<override>(G(:int)<transacts>:void)<transacts>:void = G(3)
Inc(X:int)<computes>:int = X + 1
Run(F(:int)<transacts>:int)<transacts>:int = F(1)
Forward(G(:int)<computes>:int)<transacts>:int = Run(G)
box(t:type) := class:
    Make(F(:t):void):(t->void) = F
Pick(Flag:logic):int =
    F:type{_():int} = if (Flag?) { F2 } else { F4 }
    F()
Check(Flag:logic)<computes><decides>:int =
    F:type{_(:int)<computes><decides>:int} = if (Flag?) { Identity } else { DecidesIdentity }
    F[1]
Main():void =
    Print("{Pick(true)} {Pick(false)} {Twice(One)}")
    if (V := Check[true]):
        Print("{V}")
    G := Wrap(1, TakeInt)
    G(2)
    Obj:b = b{}
    Obj.F(TakeT)
    O:?type{_():int} = option{F2}
    if (H := O?):
        Print("{H()} {Forward(Inc)}")
    K := box(int){}.Make(TakeInt)
    K(4)
