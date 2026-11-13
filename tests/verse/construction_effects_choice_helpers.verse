Seed()<reads>:int=7
box(t:type):=struct<reads>:
    Value:t
    Default:int=Seed()
Build(N:int)<reads>:int=box(int){Value:=N|N+1}.Value
M:=module:
    data<public>:=class<computes>{Value<public>:int}
    Make<public>(N:int)<computes>:data=data{Value:=N}
Main():void=
    for(X:=Build(2)):Print("choice {X}")
    F:type{_(:int)<computes>:M.data}=M.Make
    Print("qualified {F(9).Value}")
