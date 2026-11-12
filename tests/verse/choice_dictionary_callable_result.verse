ra:=class<computes>{K:int=1}
rb:=class<computes>{K:int=2}
MakeA(X:any)<computes>:ra=ra{}
MakeB(X:any)<computes>:rb=rb{}
ca:=class{F:type{_(:any)<computes>:ra}=MakeA}
cb:=class{F:type{_(:any)<computes>:rb}=MakeB}
Dup(X:t where t:type)<computes>:t=X|X
Main():void=
    Rows:=for(A:=(Dup(ca{})|Dup(cb{})),B:=(Dup(ca{})|Dup(cb{}))):A.F(B).K+B.F(A).K
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Print("{Rows.Length} {Sum}")
