vehicle:=class<allocates>{var N:int=7}
car:=class<allocates>(vehicle){Name:string="precise"}
Return(X:car)<transacts>:car=
    defer:Print("function {X.N}")
    if(V:=block{
        defer:Print("block {X.N}")
        Y:=1|2
        set X.N+=Y
        if(Y=2)then return X
        X
    },false?)then Print("bad")
    X
Break(X:car)<transacts>:car=
    loop:
        defer:Print("outer {X.N}")
        if(V:=block{
            defer:Print("break block {X.N}")
            Y:=1|2
            set X.N+=Y
            if(Y=2)then break
            X
        },false?)then Print("bad")
    X
Main()<transacts>:void=
    A:=car{}
    R:=Return(A)
    Print("return {R.Name} {A.N}")
    B:=car{Name:="b",N:=20}
    Q:=Break(B)
    Print("break {Q.Name} {B.N}")
