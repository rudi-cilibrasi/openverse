# Refining casts in source contexts (#243, #497): each lift is keyed by what
# its branch uses there. A field's default at constructions of other type
# arguments, whose declared type its lift returns, keeps one lift each; a
# parameter's default at calls that differ only in another parameter shares
# one; casts nested in a for's body, which read an outer var, are each lifted
# once (from the function made from the branch around them).
pair(a:type, b:type) := class:
    A:a
    B:b
dup(t:type) := class(pair(t, t)):
    C:int = 4
root := class{}
extra(t:type) := class(root):
    X:t
    C:int = 4
Global:root = extra(string){X := "g"}
box(a:type, b:type) := class:
    X:a
    Y:b
    N:[]a = if (D := extra[Global]) then array{} else array{}
Make(X:a, Y:b where a:type, b:type):int = box(a, b){X := X, Y := Y}.N.Length
Run(P:pair(a, b), X:c, ?N:int = if (D := dup[P]) then D.C else 0 where a:type, b:type, c:type):int = N
Use(P:pair(a, b) where a:type, b:type):int = Run(P, 1) + Run(P, "s") + Run(P, 2.5)
Nest(P0:pair(a0, b0), P1:pair(a1, b1), P2:pair(a2, b2) where a0:type, b0:type, a1:type, b1:type, a2:type, b2:type):[]int =
    var Total:int = 100
    for (I := 1..2):
        if (D0 := dup[P0]):
            if (D1 := dup[P1]):
                if (D2 := dup[P2]):
                    D0.C + D1.C + D2.C + I + Total
                else:
                    2
            else:
                1
        else:
            0
Show(Xs:[]int):string =
    var S:string = ""
    for (X : Xs) { set S = "{S}{X}," }
    S
Main():void =
    B1 := box(int, string){X := 1, Y := "y"}
    B2 := box(string, int){X := "x", Y := 2}
    Print("{B1.N.Length} {B2.N.Length} {Make(1, "s")} {Make("s", 1)}")
    Y:pair(int, int) = dup(int){A := 1, B := 2}
    Z:pair(int, string) = pair(int, string){A := 1, B := "z"}
    Print("{Use(Y)} {Use(Z)}")
    Print("{Show(Nest(Y, Y, Y))} {Show(Nest(Y, Y, Z))} {Show(Nest(Z, Y, Y))}")
