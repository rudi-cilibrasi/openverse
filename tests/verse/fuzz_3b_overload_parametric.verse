# Refused as overlapping overloads, though no value is both a box(int) and a box(string).
# LANGUAGE.md does not list two instances of one parametric class among overlapping types.
box(t:type) := class:
    Value:t
Show(B:box(int)):string = "int box {B.Value}"
Show(B:box(string)):string = "string box {B.Value}"
Main():void =
    Print(Show(box(int){Value := 1}))
    Print(Show(box(string){Value := "s"}))
