# (run with --parametric-var-fields, openverse's extension: Epic's compiler refuses a generic function over a parametric class whose mutable data holds an implicit type parameter, or a var field in a parametric interface, UEFN 43.12 errors 3552 and 3502, #724)
# a field read and set through an interface, in a class that repeats the
# interface's type arguments, where the field sits elsewhere (#157, #209)
pairish(t:type, u:type) := interface:
    var A:t
base := class:
    X:int = 0
wide(t:type, u:type) := class(base, pairish(t, u)):
    Y:int = 0
rep(t:type) := class(pairish(t, t)):
    Z:int = 0
Get(P:pairish(t, u) where t:type, u:type):t = P.A
Set(P:pairish(t, u), V:t where t:type, u:type):void = set P.A = V
Main():void =
    R := rep(int){A := 1}
    W := wide(int, string){A := 2}
    Print("{Get(R)} {Get(W)}")
    Set(R, 5)
    Set(W, 6)
    Print("{R.A} {W.A}")
