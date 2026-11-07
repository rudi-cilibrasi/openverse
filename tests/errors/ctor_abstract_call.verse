# expect: MkE constructs an abstract class: it can only be delegated to
p := class:
    A:int = 0
e := class<abstract>:
    N:int
MkE<constructor>(X:int) := e:
    N := X
Main():void = Print("{MkE(1).N}")
