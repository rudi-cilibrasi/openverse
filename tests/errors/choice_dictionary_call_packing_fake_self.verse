# expect: expected 3 argument(s), found 2
# A function's first parameter of a class type is no receiver: its arguments
# do not pack as a method's do (no parameter can be named Self: it is reserved).
ca:=class{}
Foo(This:ca,X:int,Y:int)<computes>:int=X+Y
Main():void=
    P:=ca{}
    Print("{Foo(P,(1,2))}")
