# A shared source position has identical lazy inputs but different output-only aliases.
counter := class:
    var N:int = 0
Dup(V:t where t:type):t = V | V
Lazy(C:counter, N:int)<transacts><decides>:int =
    N >= 0
    set C.N += 1
    N | Lazy[C, N - 1]
Inline(V:t, C:counter where t:type)<transacts><decides>:[]t =
    Empty:[]t = first{N := Lazy[C, 0]; N = 0; E:[]t = array{}; E}
    Empty | Empty
Main():void =
    C := counter{}
    for (V := (Dup(1) | Dup("s")), E := Inline[V, C]):
        Print("empty {E.Length}")
    Print("visits {C.N}")
