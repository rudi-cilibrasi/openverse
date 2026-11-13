vehicle:=class<allocates>{var N:int=7}
At(A:t where t:subtype([]vehicle))<computes>:int=if(V:=A[0])then V.N else -1
Main():void={}
