# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
    Tag():int = 0
strong(t:subtype(comparable)) := class(root(t)):
    Tag<override>():int = 1
weak(t:type) := class(root(t)):
    Tag<override>():int = 2
Reject(P:root(t) where t:type):void =
    Rs := for (V:=if (D:=strong[P]) then (D | D) else if (W:=weak[P]) then (W | W) else (P | P)) { V }
    for(R : Rs):
        if(NeedCmp[R.A,R.A]) then Print("bad")
Main():void = Print("unused")
