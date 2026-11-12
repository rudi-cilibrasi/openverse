# Regression: box(int) and box(string) are distinct overload domains.
# This previously failed with an overlap diagnostic.
box(t:type) := class:
    Value:t
Show(B:box(int)):string = "int box {B.Value}"
Show(B:box(string)):string = "string box {B.Value}"
Main():void =
    Print(Show(box(int){Value := 1}))
    Print(Show(box(string){Value := "s"}))
