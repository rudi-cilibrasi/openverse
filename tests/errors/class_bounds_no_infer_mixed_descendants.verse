# expect: must be comparable
NeedCmp(X:t,Y:t where t:subtype(comparable))<decides>:void = X = Y
root(t:type) := class:
    A:t
wide(t:type,u:type) := class<abstract>(root(t)):
    E:u
strong(t:subtype(comparable),u:type) := class(wide(t,u)) {}
weak(t:type,u:type) := class(wide(t,u)) {}
Reject(P:root(t) where t:type):void =
    if (D:=wide[P]):
        if (NeedCmp[P.A,P.A]) then Print("bad")
Main():void = Print("unused")
