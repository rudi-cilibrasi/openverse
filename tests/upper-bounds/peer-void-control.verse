counter:=class<allocates>{var N:int=0}
car:=class<computes>{Name:string="precise"}
Item(C:counter,V:int)<transacts>:int=
    set C.N+=1
    Print("item {C.N} {V}")
    V
Drop(X:int)<computes>:void=X
DropArray(X:[]int)<computes>:[]void=X
DropOption(X:?int)<computes>:?void=X
Main():void=
    C:=counter{}
    V:void=Drop(Item(C,7))
    Print("discarded {C.N}")
    if(Drop(Item(C,8)),false?)then Print("bad")else Print("rolled discard")
    A:=DropArray(array{Item(C,9),Item(C,10)})
    Print("array {A.Length} {C.N}")
    O:=DropOption(option{Item(C,11)})
    if(O?)then Print("some {C.N}")else Print("bad")
    N:=DropOption(false)
    if(N?)then Print("bad")else Print("none {C.N}")
    R:=car{}
    Print("{R.Name} {C.N}")
