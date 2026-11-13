# expect: 6:14: int has no method 'Ext'
# An extension method of a module the call does not open is not found
Sub := module:
    (A:int).Ext<public>():int = A
Main():void =
    X := 1.Ext()
