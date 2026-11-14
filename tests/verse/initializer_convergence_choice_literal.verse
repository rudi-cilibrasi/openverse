c:=class<computes>{Value:int=if(V:=first{1|2})then V else 0}
Main():void=for(C:=(c{}|c{})):Print("{C.Value}")
