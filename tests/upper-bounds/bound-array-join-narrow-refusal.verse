vehicle:=class<computes>{N:int=1}
car:=class<computes>(vehicle){}
Join(A:[]a,B:[]b where a:subtype(vehicle),b:subtype(vehicle))<computes>:[]car=A+B
Main():void={}
