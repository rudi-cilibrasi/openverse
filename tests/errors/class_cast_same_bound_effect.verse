# expect: Bad calls Mark, which has the effect <writes>
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){Hi:int=2}
Add(X:int,Y:int)<computes>:int=X+Y
cell:=class{var N:int=0}
Mark(H:cell)<writes>:int=(set H.N=1;0)
Bad(H:cell,P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<computes><decides>:int=
    first{I:=0..Add(dup[P].Hi,dup[Q].Hi)+Mark(H);I>0;I}
Main():void={}
