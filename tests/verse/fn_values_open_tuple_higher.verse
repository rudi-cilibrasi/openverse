Id(X:t where t:type)<computes>:t=X
Make(X:t where t:type)<computes>:type{_(:t)<computes>:t}=Id
Apply(F:type{_(:t)<computes>:u},X:t where t:type,u:type)<computes>:u=F(X)
Run(X:a,Y:b where a:type,b:type)<computes>:tuple(a,b)=
    Factory:type{_(:a,:b)<computes>:type{_(:tuple(a,b))<computes>:tuple(a,b)}}=Make
    F:=Factory(X,Y)
    G:type{_(:tuple(type{_(:tuple(a,b))<computes>:tuple(a,b)},tuple(a,b)))<computes>:tuple(a,b)}=Apply
    G((F,(X,Y)))
Main():void=
    R:=Run(7,"s")
    Print("{R(0)} {R(1)}")
