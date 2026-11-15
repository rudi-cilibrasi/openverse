# expect: is not a var
pair(a:type,b:type):=class{}
dup(t:type):=class(pair(t,t)){Index:int=0}
Bad(P:pair(a,b) where a:type,b:type)<decides>:int=
    A:[]int=array{0}
    set A[dup[P].Index]=7
    0
Main():void={}
