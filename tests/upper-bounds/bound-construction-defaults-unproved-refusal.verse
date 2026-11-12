vehicle:=class<computes>{N:int=7}
holder(t:subtype(vehicle)):=class<computes>{Value:t}
Make(X:t where t:type)<computes>:holder(t)=holder(t){Value:=X}
Main():void={}
