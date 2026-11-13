# (#283) A <computes> recursive function whose values' code prints (a
# constructed class's block:) is taken lazily, and its call of itself in a
# field of a class's construction is a choice point there, in the class's
# field order, the elaborator's, as an earlier elaboration noted it. It was
# refused, the field order of a class unknown to the lifter.
box := class<computes>:
    D:int = 1+2
    V:int
    block:
        Print("block")
R(N:int)<computes>:int =
    if (N>0) then (N | R(box{V:=N|N+1}.V-2)) else 0
Main():void = for (V := R(2)): Print("{V}")
