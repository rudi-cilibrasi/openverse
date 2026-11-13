vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
reader:=class<computes>:
    Read(X:vehicle)<reads>:vehicle=X
Build(X:car)<computes>:type{_(:car)<reads>:vehicle}=reader{}.Read
Main():void=
    C:=car{N:=7}
    F:=Build(C)
    Print("method {F(C).N}")
