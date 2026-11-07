# regression test from the #53 review (p80a)
two(a:type, b:type) := interface:
    A:a
    B:b
    GetB():b = B
dup(t:type) := class(two(t, t)):
    N:int = 0
Main():void =
    D := dup(int){A := 1, B := 2}
    Print("{D.GetB()}")
