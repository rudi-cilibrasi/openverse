# expect: must be comparable
Id(X:t where t:type)<transacts>:t=X
Same(X:t,Y:t where t:subtype(comparable))<decides>:t=
    X=Y
    X
Use(X:t where t:type)<transacts><decides>:void=
    F:type{_(:t)<transacts>:t}=Id
    F(X)=X
Main():void=
    if (Use[1]) then Print("wrong")
