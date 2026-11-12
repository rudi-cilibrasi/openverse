la:=class{var X:int=0}
lb:=class{var X:int=0}
ca:=class{Items:[]la}
cb:=class{Items:[]lb}
Dup(X:t where t:type)<computes>:t=X|X
Use(P:ca,Q:cb)<writes>:int=
    Rows:=for(A:=(Dup(P)|Dup(Q)),set A.Items[0].X+=7):0
    Rows.Length
Main():void=
    P:=ca{Items:=array{la{}}}
    Q:=cb{Items:=array{lb{}}}
    Print("{Use(P,Q)}")
