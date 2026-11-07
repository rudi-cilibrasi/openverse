# expect: MkC delegates to MkA, which delegates in a cycle
p := class:
    A:int = 0
MkC<constructor>() := p:
    MkA<constructor>()
MkA<constructor>() := p:
    MkB<constructor>()
MkB<constructor>() := p:
    MkA<constructor>()
Main():void = Print("x")
