# a function with one tuple parameter as a value at the flattened type,
# also a generic one at an instance (#231)
First(P:tuple(int, string)):int = P(0)
Swap(P:tuple(t, u) where t:type, u:type):tuple(u, t) = (P(1), P(0))
Apply2(F:type{_(:int, :string):int}):int = F(4, "x")
Main():void =
    Print("{Apply2(First)}")
    G:type{_(:int, :string):tuple(string, int)} = Swap
    R := G(1, "a")
    Print(R(0))
