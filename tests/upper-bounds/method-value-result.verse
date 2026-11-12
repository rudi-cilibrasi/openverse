vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
box(a:subtype(vehicle)):=class<computes>:
    X:a
    Get()<computes>:a=X
Build(X:t where t:subtype(vehicle))<computes>:type{_()<computes>:vehicle}=box(t){X:=X}.Get
Main():void=
    C:=car{N:=7}
    F:=Build(C)
    Print("result {F().N}")
