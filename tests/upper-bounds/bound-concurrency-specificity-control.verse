worker:=class(event(int)):
    Await()<computes>:int=7
holder:=class<computes>{Value:worker}
Use(X:worker,H:holder)<computes>:int=X.Await()
Reverse(H:holder,X:worker)<computes>:int=X.Await()
Main():void=
    W:=worker{}
    H:=holder{Value:=W}
    Print("ordinary {Use(W,H)} {Reverse(H,W)}")
