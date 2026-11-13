counter:=class<allocates>{var N:int=0}
Tick(C:counter)<transacts>:int=(set C.N+=1;C.N)
Show(X:int,C:counter)<computes>:string="{Tick(C)}:{X}"
Main():void={}
