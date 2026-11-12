ca:=class{}
Foo(Self:ca,X:int,Y:int)<computes>:int=X+Y
Main():void=
    P:=ca{}
    Print("{Foo(P,(1,2))}")
