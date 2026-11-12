vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){Name:string="precise"}
box:=class<computes>:
    X:car
    Get()<computes>:car=X
Build(X:car)<computes>:type{_()<computes>:vehicle}=box{X:=X}.Get
Main():void=
    C:=car{N:=7}
    F:=Build(C)
    Print("result {F().N}")
