car:=class<computes>{Name:string="precise"}
Copy(Base:void,X:car)<computes>:car=X
Main():void=
    V:void=7
    R:=Copy(V,car{})
    Print("{R.Name}")
