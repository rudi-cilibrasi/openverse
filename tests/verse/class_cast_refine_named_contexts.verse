pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
reader:=class:
    Pick(?Index:int=0):int=Index
Pack(X:t,?Other:[]t=array{} where t:type):[]t=Other
Choose(P:pair(a,b) where a:type,b:type)<decides>:b=
    R:=reader{}.Pick(?Index:=dup[P].Index)
    Values:=Pack(P.A,?Other:=array{dup[P].B})
    Values[0]
Main():void=
    P:=dup(int){A:=7,B:=9}
    if(V:=Choose[P])then Print("if {V}")
    O:=option{Choose[P]}
    if(V:=O?)then Print("option {V}")
    for(V:=Choose[P]){Print("for {V}")}
    if(V:=first{W:=Choose[P];W})then Print("first {V}")
