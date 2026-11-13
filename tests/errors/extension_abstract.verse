# expect: 5:0: expected '=' before the extension method's body
# An extension method in a class has a body
c := class:
    (I:int).Get():int
Main():void = {}
