car:=class<computes>{Name:string="precise"}
Copy(Base:t,X:u where t:subtype(comparable),u:subtype(t))<computes>:u=X
Main():void=
    V:void=7
    R:=Copy(V,car{})
    Print("{R.Name}")
