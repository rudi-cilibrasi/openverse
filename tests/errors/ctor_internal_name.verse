# expect: MkP<constructor> cannot fail: call it with MkP<constructor>(…)
p := class:
    A:int = 0
MkP<constructor>(X:int) := p:
    A := X
MkQ<constructor>(X:int) := p:
    MkP<constructor>[X]
Main():void = Print("x")
