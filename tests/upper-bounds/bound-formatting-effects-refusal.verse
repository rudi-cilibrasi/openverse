counter:=class<allocates>{var N:int=0}
Tick(C:counter)<transacts>:int=(set C.N+=1;C.N)
Show(X:t,C:counter where t:subtype(int))<computes>:string="{Tick(C)}:{X}"
Main():void={}
