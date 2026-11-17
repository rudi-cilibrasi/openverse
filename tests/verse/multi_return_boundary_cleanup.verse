F(X:int)<transacts>:int=
    var Saved:int=X
    defer:
        Print("function {Saved}")
        set Saved+=1000
    loop:
        defer:
            Print("loop {Saved}")
            set Saved+=100
        if(Saved=X):
            defer:
                Print("branch {Saved}")
                set Saved+=10
            return Saved
    X|X+1
Main()<transacts>:void=
    for(V:=F(5)){Print("v {V}")}
    Print("after")
