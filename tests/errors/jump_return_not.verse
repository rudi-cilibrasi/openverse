# expect: 4:20: return cannot leave a failure context
# A return in the operand of not
F(X:int):int =
    if (not (X = 1, return 5)) then 1 else 2
Main():void = Print("{F(1)}")
