cell:=class{var N:int=0}
box(t:type,h:type):=class:
    Hidden:h
    C:cell
    Echo(X:t):t=
        set C.N+=1
        Print("echo {C.N}")
        X
Bind(B:box(tuple(a,b),c) where a:type,b:type,c:type):type{_(:a,:b):tuple(a,b)}=B.Echo
Run(B:box(tuple(a,b),c),X:a,Y:b where a:type,b:type,c:type):tuple(a,b)=
    F:=Bind(B)
    set B.C.N+=4
    F(X,Y)
Main():void=
    R:=Run(box(tuple(int,int),string){Hidden:="hidden",C:=cell{}},2,21)
    Print("result {R(0)} {R(1)}")
