vehicle:=class<computes>{N:int=0}
holder(t:subtype(vehicle)):=class<computes>:
    X:t
    Touch()<transacts>:void=set X.N=1
Main():void={}
