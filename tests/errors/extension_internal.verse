# expect: 7:14: int has no method 'Ext'
# An internal extension method of a module is not found outside it
Sub := module:
    (A:int).Ext():int = A
using { Sub }
Main():void =
    X := 1.Ext()
