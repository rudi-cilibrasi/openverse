# expect: has the effect <writes>
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){Index:int=0}
cell:=class{var N:int=0}
Write(H:cell)<writes>:int=(set H.N=1;7)
Bad(H:cell,P:pair(a,b) where a:type,b:type)<computes><decides>:int=
    var A:[]int=array{0}
    set A[dup[P].Index]=Write(H)
    A[0]
Main():void={}
