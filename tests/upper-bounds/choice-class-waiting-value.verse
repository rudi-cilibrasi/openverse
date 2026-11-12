vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
box(a:subtype(vehicle)):=class<computes>:
    Item:a
    Read()<reads>:int=Item.N
Dup(X:t where t:type)<computes>:t=X|X
Run(X:t where t:subtype(vehicle))<suspends>:[]box(t)=
    B:=box(t){Item:=X}
    for(A:=Dup(B)):
        Sleep(0.1)
        A
Main()<suspends>:void=
    C:=car{}
    R:=Run(C)
    set C.N=9
    if(B:=R[0]):
        F:type{_()<reads>:int}=B.Read
        Print("{R.Length} {B.Item.Name} {F()}")
