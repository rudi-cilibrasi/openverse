Dup(X:int)<computes>:int=X|X
c:=class<computes>{Value:int=if(V:=first{Dup(3)})then V else 0}
Main():void=for(C:=(c{}|c{})):Print("{C.Value}")
