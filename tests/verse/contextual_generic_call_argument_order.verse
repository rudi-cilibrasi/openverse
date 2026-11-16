cell:=class{var Trace:string=""}
Note(H:cell,S:string,N:int)<transacts>:int={set H.Trace+=S;N}
Empty(H:cell,?Count:int=Note(H,"D",0),?Default:?t=false where t:type)<transacts>:?t=Default
Choose(M:[?int]t,Other:t where t:type):t=Other
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Index:int=0}
Leaf(X:t,?Index:int=0 where t:type):t=X
Value(H:cell,S:string,X:t where t:type)<transacts>:t={set H.Trace+=S;X}
Refined(P:pair(a,b),Q:pair(c,d),H:cell where a:type,b:type,c:type,d:type)<decides>:b=
    Choose(map{Empty(H)=>Leaf(Value(H,"V",P.A),?Index:=dup[Value(H,"Q",Q)].Index)},Value(H,"O",dup[Value(H,"P",P)].B))
Main()<transacts>:void=
    H:=cell{}
    V:=Choose(map{Empty(H,?Count:=Note(H,"K",0))=>Note(H,"V",7)},Note(H,"O",9))
    Print("named {V} {H.Trace}")
    set H.Trace=""
    D:=Choose(map{Empty(H)=>Note(H,"V",7)},Note(H,"O",9))
    Print("default {D} {H.Trace}")
    set H.Trace=""
    if(R:=Choose(map{Empty(H)=>Note(H,"V",7)},Note(H,"O",9)),false?)then Print("wrong")
    Print("rollback '{H.Trace}'")
    P:=dup(int){A:=7,B:=9}
    Q:=dup(string){A:="left",B:="right"}
    if(RV:=Refined[P,Q,H])then Print("refined {RV} {H.Trace}")else Print("wrong")
    set H.Trace=""
    if(RV:=Refined[P,pair(int,string){A:=1,B:="bad"},H])then Print("wrong")else Print("value rollback '{H.Trace}'")
    if(RV:=Refined[pair(int,string){A:=1,B:="bad"},Q,H])then Print("wrong")else Print("later rollback '{H.Trace}'")
    if(RV:=Refined[P,Q,H],false?)then Print("wrong")else Print("outer rollback '{H.Trace}'")
