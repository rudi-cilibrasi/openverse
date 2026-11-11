cell:=class{var N:int=0}
Tick(C:cell,Tag:string):int=
    set C.N+=1
    Print("{Tag} {C.N}")
    C.N
box:=class:
    C:cell
    Same(X:t where t:type):t=
        A:=Tick(C,"same")
        X
Touch(B:box):box=
    A:=Tick(B.C,"receiver")
    B
applicator(t:type):=class:
    V:t
    C:cell
    Apply(F:type{_(:u):u},?X:u,?N:int=Tick(C,"default") where u:subtype(comparable)):int=if(F(X)=X)then 1 else -1
Run(A:applicator(a),B:box where a:type):int=A.Apply(Touch(B).Same,?X:=Tick(B.C,"arg"))
Main():void=
    C:=cell{}
    R:=Run(applicator(string){V:="tag",C:=C},box{C:=C})
    Print("result {R} {C.N}")
