# expect: 3:0: 'first' is reserved: no definition can take it
# An extension method cannot take a reserved name
(X:int).first():int = X
Main():void = {}
