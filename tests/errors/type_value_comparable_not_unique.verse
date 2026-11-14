# expect: expected concrete_subtype(comparable), found p
p := class<concrete>:
    N:int = 0
Main():void =
    X:concrete_subtype(comparable) = p
