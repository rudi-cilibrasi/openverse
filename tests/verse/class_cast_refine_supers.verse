# Refining casts' branches in methods calling (super:) (#243): at the refined object's values, nested in its
# own arguments, through a chain of three classes, an interface's default, in a void method
pair(t:type, u:type) := class:
    A:t
    B:u
dup(t:type) := class(pair(t, t)):
    C:int = 0
named := interface:
    Tag(N:int):string = "named{N}"
base := class(named):
    Name(N:int):string = "base{N}"
    Twice(N:int):int = N * 2
mid := class(base):
    Name<override>(N:int):string = "mid{N}"
    Twice<override>(N:int):int = N * 3
top := class(mid):
    Name<override>(N:int):string = "top{N}"
    Tag<override>(N:int):string = "top-tag"
    Get(P:pair(a, b), X:a where a:type, b:type):b =
        if (D := dup[P]):
            Print((super:)Name(D.C))
            Print("{(super:)Twice((super:)Twice(D.C))}")
            Print((super:)Tag(D.C + 1))
            X
        else:
            P.B
    Show(P:pair(a, b) where a:type, b:type)<transacts>:void =
        if (D := dup[P]):
            Print((super:)Name(100))
Main()<transacts>:void =
    Print("{top{}.Get(dup(int){A := 1, B := 2, C := 4}, 3)}")
    Print("{top{}.Get(pair(int, string){A := 1, B := "x"}, 3)}")
    top{}.Show(dup(int){A := 1, B := 2})
