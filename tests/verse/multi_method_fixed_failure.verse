meter := class:
    var N:int = 0
root(t:type) := class:
    H:meter
    Both()<transacts><decides>:int = 1 | 2
fixed := class(root(int)):
    Both<override>()<transacts><decides>:int =
        set H.N += 1
        Print("fail")
        false?
        3 | 4
Main()<transacts>:void =
    H := meter{}
    X:root(int) = fixed{H:=H}
    if (V := X.Both[]) then Print("bad {V}") else Print("none {H.N}")
    R := for (V := X.Both[]) { Print("bad {V}"); V }
    Print("end {R.Length} {H.N}")
