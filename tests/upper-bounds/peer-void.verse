counter:=class<allocates>{var N:int=0}
car:=class<computes>{Name:string="precise"}
Item(C:counter,V:int)<transacts>:int=
    set C.N+=1
    Print("item {C.N} {V}")
    V
Upper(Base:t,Value:u where t:type,u:subtype(t))<computes>:t=Value
Keep(X:t where t:subtype(void))<computes>:t=X
KeepZero(X:t where t:subtype(tuple()))<computes>:t=X
Main():void=
    C:=counter{}
    V:void=Upper((),Item(C,7))
    Print("discarded {C.N}")
    if(Upper((),Item(C,8)),false?)then Print("bad")else Print("rolled discard")
    A:[]void=Upper(array{()},array{Item(C,9),Item(C,10)})
    Print("array {A.Length} {C.N}")
    Base:?void=false
    O:?void=Upper(Base,option{Item(C,11)})
    if(O?)then Print("some {C.N}")else Print("bad")
    Empty:?int=false
    N:?void=Upper(Base,Empty)
    if(N?)then Print("bad")else Print("none {C.N}")
    R:=Keep(KeepZero(car{}))
    Print("{R.Name} {C.N}")
