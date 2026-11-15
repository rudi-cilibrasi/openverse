reader:=class<unique>{N:int;Read()<computes>:int=N}
Probe(R:reader)<transacts>:reader=
    Print("right operand evaluated")
    R
Index()<transacts>:int=
    Print("index evaluated")
    0
Same(A:reader,B:reader)<computes><decides>:reader=A=B
Main():void=
    A:=reader{N:=11}
    B:=reader{N:=22}
    if(Alias:=A=Probe(A))then Print("equality {Alias.Read()}")
    if(Alias:=A<>Probe(B))then Print("inequality {Alias.Read()}")
    if(Alias:=Same[A,A])then Print("helper {Alias.Read()}")
    if(Values:=array{A}=array{A},Alias:=Values[0])then Print("array equality {Alias.Read()}")
    Items:=array{A,B}
    if(Alias:=Items[Index()])then Print("index {Alias.Read()}")
    var Updated:[]reader=Items
    if(set Updated[Index()]=B,Alias:=Updated[0])then Print("updated {Alias.Read()}")
