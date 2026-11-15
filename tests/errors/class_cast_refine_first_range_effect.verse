# expect: Bad calls Mark, which has the effect <writes>
# The bound-probing pass must not hide the actual bound call's effects.
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){Hi:int=2}
cell:=class:
    var N:int=0
Mark(H:cell)<writes>:int=(set H.N=1;0)
Bad(H:cell,P:pair(a,b) where a:type,b:type)<computes><decides>:int=
    first{I:=0..dup[P].Hi+Mark(H);I>0;I}
Main():void={}
