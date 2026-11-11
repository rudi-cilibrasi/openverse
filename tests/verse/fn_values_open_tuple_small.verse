Id(X:t where t:type)<computes>:t=X
Head(X:tuple(t) where t:type)<computes>:t=X(0)
Run(X:t where t:type)<computes>:tuple(t,tuple(t))=
    F:type{_(:tuple(t))<computes>:t}=Id
    G:type{_(:t)<computes>:t}=Head
    H:type{_(:t)<computes>:tuple(t)}=Id
    (F(H(G(X))),H(X))
Main():void=
    R:=Run(9)
    Print("{R(0)} {R(1)(0)}")
    F:type{_()<computes>:tuple()}=Id
    E:=F()
    Print("empty")
