# expect: shape is <abstract>: it cannot be constructed
shape := class<abstract>:
    N:int = 0
Main():void =
    S := shape{}
