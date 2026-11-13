vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
reader:=class<computes>:
    Read(X:vehicle)<reads>:vehicle=X
Build(X:t where t:subtype(vehicle))<computes>:type{_(:t)<reads>:vehicle}=reader{}.Read
Main():void=
    C:=car{N:=7}
    F:=Build(C)
    Print("method {F(C).N}")
