vehicle:=class<allocates>{var N:int=7}
Replace(A:t,X:vehicle where t:subtype([]vehicle))<transacts><decides>:void=
    var B:t=A
    set B[0]=X
Main():void={}
