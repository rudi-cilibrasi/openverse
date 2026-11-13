vehicle:=class<allocates>{var N:int=0}
holder(t:subtype(vehicle)):=class<computes>:
    X:t
    Touch()<computes>:void=set X.N=1
Main():void={}
