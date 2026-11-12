Dup(X:int)<computes>:int=X|X
c:=class<computes>{Value:int=first{Dup(3)}}
Main():void=for(C:=(c{}|c{})):Print("{C.Value}")
