# expect: MkP<constructor>(…) delegates to a constructor: it can only be an item of a constructor
p := class:
    A:int = 0
MkP<constructor>() := p:
    A := 1
Main():void =
    MkP<constructor>()
