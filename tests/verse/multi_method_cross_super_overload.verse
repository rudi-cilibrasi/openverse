# A scalar overloaded target retains ancestor lookup and argument binding.
base := class:
    Read(N:int,?M:int=N)<transacts>:int = N+M
    Read(S:string)<transacts>:int = S.Length
child := class(base):
    Values()<transacts>:int =
        (super:)Read(3,?M:=4)|(super:)Read("word")
    Read<override>(N:int,?M:int=N)<transacts>:int = 99
Main():void = for(V:=child{}.Values()): Print("{V}")
