# expect: 7:4: pair.Vals has several values, but pair is below both left and right, which declare Vals apart
left := interface:
    Vals()<transacts>:int
right := interface:
    Vals()<transacts>:int
pair := class(left, right):
    Vals<override>()<transacts>:int = 1 | 2
Main()<transacts>:void =
    for (X := pair{}.Vals()):
        Print("{X}")
