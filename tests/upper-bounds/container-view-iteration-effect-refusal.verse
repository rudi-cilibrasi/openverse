vehicle:=class<allocates>{var N:int=1}
Read(A:t where t:subtype([]vehicle))<computes>:[]int=for(X:A):X.N
Main():void={}
