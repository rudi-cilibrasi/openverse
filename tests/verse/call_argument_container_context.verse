# Generic function values obtain their expected type inside contextual containers.
Id(X:t where t:type)<computes>:t=X
K(X:t where t:type)<computes>:int=7
Opt(P:tuple(?type{_(:int)<computes>:int}))<computes>:int=
    if(G:=P(0)?)then G(7)else 0
Map(P:tuple([int]type{_(:int)<computes>:int}))<computes>:int=
    if(G:=P(0)[1])then G(7)else 0
Main():void=
    Print("{Opt(option{Id})} {Opt(option{K})} {Map(map{1=>K})}")
