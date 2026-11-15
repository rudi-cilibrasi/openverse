# expect: expected b, found a
# A conditional first index cannot export its local refinement when a
# mandatory cast in a later index triggers lifting of the whole path.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){Index:int=0}
Bad(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<decides>:b=
    var A:[][]int=array{array{0}}
    set A[if(D:=dup[P])then D.Index else 0][dup[Q].Index]=7
    P.A
Main():void={}
