vehicle:=class{Speed:int=1}
car:=class(vehicle){Doors:int=2}
Process(X:t where t:subtype(vehicle))<computes>:t=X
Main():void=Print("{Process(car{}).Doors}")
