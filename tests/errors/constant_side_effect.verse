# expect: the value of the constant J calls Bump, which has the effect <writes>: a module's constant has no side effect
counter := class{ var N:int = 0 }
Bump():int =
    C := counter{}
    set C.N += 1
    C.N
J:int = Bump()
Main():void = Print("{J}")
