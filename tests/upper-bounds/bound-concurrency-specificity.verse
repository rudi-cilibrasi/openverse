worker:=class(event(int)):
    Await()<computes>:int=7
holder(t:subtype(event(int))):=class<computes>{Value:t}
Use(X:t,H:holder(t) where t:subtype(worker))<computes>:int=X.Await()
Reverse(H:holder(t),X:t where t:subtype(worker))<computes>:int=X.Await()
Main():void=
    W:=worker{}
    H:=holder(worker){Value:=W}
    Print("ordinary {Use(W,H)} {Reverse(H,W)}")
