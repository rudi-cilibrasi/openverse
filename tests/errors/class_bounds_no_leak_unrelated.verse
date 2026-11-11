# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
    Hit(N:t):int = 0
tight(t:subtype(comparable)) := class(root(t)):
    Hit<override>(N:t):int = if (A=N) then 1 else 2
Reject(P:root(t),V:u where t:type,u:type):void =
    if (D:=tight[P]):
        if (NeedCmp[V,V]) then Print("bad")
Main():void = Print("unused")
