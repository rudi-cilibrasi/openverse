vehicle:=class<allocates>{var N:int=1}
car:=class<allocates>(vehicle){}
Bad(X:t,?V:int=X.N where t:type)<reads>:int=V
Wrapper(X:t where t:subtype(vehicle))<reads>:int=Bad(X)
Main():void=Print("{Wrapper(car{})}")
