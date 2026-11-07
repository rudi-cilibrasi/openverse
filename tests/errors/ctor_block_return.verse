# expect: return is not allowed in a block: clause
p := class:
    A:int = 0
MkP<constructor>() := p:
    block:
        return
Main():void = Print("{MkP().A}")
