# expect: this call of G fits more than one overload: (int) and ([]int)
# G(:int) beside G(:[]int) are two overloads (#724,
# tests/verse/overload_scalar_array), and a call whose argument is a tuple
# of one int fits both: its element for the first, an array for the second.
G(X:int):string = "one"
G(X:[]int):string = "many"
One(X:tuple(u) where u:type)<computes>:tuple(u)=X
Main():void =
    P:type{_(:int)<computes>:tuple(int)} = One
    Print("{G(P(1))}")
