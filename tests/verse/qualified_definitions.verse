# Qualified definitions and uses (docs/research/qualified-names.md): a
# definition's qualifier names where it is defined (its module, its class,
# its enum or struct); a use looks the name up in the scope its qualifier
# names, and nowhere else.
Top := module:
    (Top:)A<public> := module:
        (Top.A:)Value<public>:int = 1
        (Top.A:)Twice<public>(X:int):int = 2 * X
        (A:)counter<public> := class:
            (counter:)Step:int = 5
            var (counter:)Total<public>:int = 0
            (Top.A.counter:)Add<public>():int =
                set (counter:)Total += (counter:)Step + Self.(counter:)Step
                (counter:)Total
            (counter:)Bonus():int = 100
            Both<public>():int = (counter:)Add() + (counter:)Bonus()
        (Top.A:)keyword<public> := enum{(keyword:)for, (keyword:)if, (keyword:)keyword}
        (Top.A:)pair<public> := struct{(pair:)L:int, (pair:)R:int}
    (Top:)Sum<public>(P:A.pair):int = P.L + P.R
# a class's member may be qualified with its own class, beside a top-level
# definition of the same name (Book of Verse ch. 10)
Shade(X:int):int = X + 1
shaded := class:
    (shaded:)Shade(X:int):int = X + 2
Main():void =
    Print("{(Top.A:)Value} {(Top.A:)Twice(4)} {Top.A.(Top.A:)Value} {Top.A.(Top.A:)Twice(5)}")
    C := (Top.A:)counter{}
    Print("{C.Add()} {C.Add()} {C.(Top.A.counter:)Total} {C.Both()}")
    if ((Top.A.keyword:)for <> (Top.A.keyword:)if, (Top.A.keyword:)keyword = Top.A.keyword.keyword):
        Print("an enum's values may be named like keywords when qualified")
    Print("{(Top:)Sum((Top.A:)pair{L := 3, R := 4})}")
    Print("{Shade(1)} {shaded{}.Shade(1)} {shaded{}.(shaded:)Shade(1)}")
