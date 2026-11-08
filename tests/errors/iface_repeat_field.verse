# expect: rep repeats its type arguments or fixes them to types that mention type parameters: reading it is not supported yet
pairish(t:type, u:type) := interface:
    var A:t
base := class:
    X:int = 0
wide(t:type, u:type) := class(base, pairish(t, u)):
    Y:int = 0
rep(t:type) := class(pairish(t, t)):
    Z:int = 0
Get(P:pairish(t, u) where t:type, u:type):t = P.A
Main():void = Print("{Get(rep(int){A := 1})}")
