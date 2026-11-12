# Differing callback effects retain their original call behavior.
cell:=class{var N:int=0}
Read(H:cell,X:int)<reads>:int=block{Print("a {H.N}");1}
Write(H:cell,X:int)<transacts>:int=block{Print("b {H.N}");set H.N+=X;2}
ca:=class{V:int=1;F:type{_(:cell,:int)<reads>:int}}
cb:=class{V:int=2;F:type{_(:cell,:int)<transacts>:int}}
Argument(H:cell,X:int)<transacts>:int=block{set H.N+=1;Print("arg {H.N}");X}
Dup(X:t where t:type)<computes>:t=X|X
Keep(X:t where t:subtype(comparable))<computes>:int=if(X=X)then 1 else 0
Main():void=
    H:=cell{}
    Rows:=for(A:=(Dup(ca{F:=Read})|Dup(cb{F:=Write})),B:=(Dup(1)|Dup("s"))):A.F(H,Argument(H,A.V))+Keep(B)
    var Sum:int=0
    for(Row:Rows):set Sum+=Row
    Print("{Rows.Length} {Sum} {H.N}")
