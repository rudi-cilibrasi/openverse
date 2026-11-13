# expect: X.(b:)F: b does not introduce F, it inherits it: a qualifier names where the method is defined, (a:)
a := class:
    F():int = 1
b := class(a){}
c := class(b):
    G():int = (b:)F()
Main():void = {}
