# A construction may name its type in parentheses, as a type is written
# (Book of Verse tests: `F():void=(t(int)){}`, `(c1()){X:=10}`), with its
# fields in braces or, after a `:` that ends the line, indented.
box(t:type) := class:
    V:int = 3
point := struct:
    X:int = 1
    Y:int = 2
Main():void =
    K := (box(int)){}
    P := (point){Y := 20}
    Q := (point):
        X := 5
    R := case(P.Y):
        20 => "twenty"
        _ => "other"
    Print("{K.V} {P.X} {P.Y} {Q.X} {R} {(1 + 2) * 3}")
