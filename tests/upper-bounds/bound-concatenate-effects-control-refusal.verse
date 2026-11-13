counter:=class<allocates>{var N:int=0}
Take(A:t,C:counter where t:type)<transacts>:t=(set C.N+=1;A)
Flatten(A:[][]int,C:counter)<computes>:[]int=Concatenate(Take(A,C))
Main():void={}
