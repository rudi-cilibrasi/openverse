# Function values of functions with named parameters (#503), the pinned Book
# of Verse's examples (ch. 6, "Named Parameters", and its DefaultNamed tests):
# names are part of a function type, a parameter with a default may be left
# out of it, `?N:t = e` lets a caller of the value omit N (the function's own
# default runs, not e), and a value keeps its own named type unannotated.
Process(?Required:int, ?Optional:int = 0):int = Required + Optional
DefaultAll(?A:int = 1, ?B:int = 2):int = A + B
Seven(?X:int = 7)<computes>:int = X
F1(?X:int = 1):int = X
Mixed(A:int, ?B:int = 0, ?C:int):int = A + B - C
A1(?A:int):int = A
F2(?A:int = 2):int = A
F4(?B:int = 4):int = B
F6(?A:int = 6):int = A
F9(?A:int = 9, ?B:int = 10):int = A + B
Join1(F:type{_(?A:int):int}):int = F(?A := 1)
Join2(F:type{_(?A:int = 0):int}):int = F() + F(?A := 2)
Coerce(A:[]int, ?B:int = 2):[]int =
    for (X : A):
        X + B
Main():void =
    P1:type{_(?Required:int):int} = Process
    P2:type{_(?Required:int, ?Optional:int):int} = Process
    P3:type{_():int} = DefaultAll
    Print("{P1(?Required := 5)} {P2(?Required := 5, ?Optional := 3)} {P3()}")
    S:type{_()<computes>:int} = Seven
    Print("{S()}")
    # (the type's default is not part of it: F1's own runs)
    X:type{_(?X:int = 99):int} = F1
    Print("{X()} {X(?X := 5)}")
    M := Mixed
    Print("{M(1, ?C := 2)} {M(1, ?C := 2, ?B := 3)}")
    Sub1:type{_():int} = F2
    Sub2:type{_(?A:int):int} = F2
    Print("{Sub1()} {Sub2(?A := 1)}")
    # (a branch of each type at one expected type; the joined values)
    Meet1:type{_():int} = if (true?) then F2 else F4
    Meet2:type{_():int} = if (false?) then F2 else F4
    Meet3:type{_(?A:int):int} = if (true?) then A1 else F2
    Print("{Meet1()} {Meet2()} {Meet3(?A := 1)}")
    J1:type{_(:type{_(?A:int = 0):int}):int} = if (true?) then Join1 else Join2
    J2:type{_(:type{_(?A:int = 0):int}):int} = if (false?) then Join1 else Join2
    Print("{J1(F6)} {J2(F6)}")
    Both:type{_(?A:int, ?B:int):int} = F9
    Print("{Both(?B := 1, ?A := 2)}")
    G:type{_(:[]int):[]int} = Coerce
    R := G(1, 2)
    Print("{R.Length} {if (V := R[0]) then V else 0} {if (V := R[1]) then V else 0}")
