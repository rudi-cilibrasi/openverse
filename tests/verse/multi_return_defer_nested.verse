# Return operands are saved before inner-to-outer cleanup mutates the heap.
cell := class { var N:int=0 }
Nested(H:cell,Mode:int)<transacts>:int =
    defer:
        Print("outer {H.N}")
        set H.N+=100
    if(Mode>=0):
        defer:
            Print("branch {H.N}")
            set H.N+=10
        if(Mode>0):
            defer:
                Print("inner {H.N}")
                set H.N+=1
            if(Mode=2):
                return block{Print("operand");set H.N=7;H.N}
            Print("inner fallthrough")
        Print("branch fallthrough")
    Print("tail")
    H.N|H.N+1
Main():void =
    for(Mode:array{2,0}):
        H:=cell{}
        Print("case {Mode}")
        for(V:=Nested(H,Mode)):Print("value {V} state {H.N}")
