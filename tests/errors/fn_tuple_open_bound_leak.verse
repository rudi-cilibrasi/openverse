# expect: must be comparable
Id(X:t where t:type):t=X
Same(X:t where t:subtype(comparable)):t=X
Run(X:a,Y:b where a:type,b:type)<decides>:void=
    F:type{_(:a,:b):tuple(a,b)}=Id
    R:=F(X,Y)
    R(0)=X
Main():void=
    if(Run[3,"s"])then Print("wrong")
