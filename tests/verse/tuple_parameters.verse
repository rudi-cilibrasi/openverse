# Destructured tuple parameters (Book of Verse ch. 6, "Tuple as Arguments",
# and its NestedTupleParameters tests): a parenthesized group of parameters
# is one parameter of the tuple type, its names bound to the elements, so a
# tuple literal, a tuple variable or the whole argument list as one tuple
# can be given; groups nest, and a group of one parameter is that parameter.
# It is a tuple parameter for overloads, function values and defaults too.
F(A:int, (B:int, C:int), D:int):int = A + B + C + D
G(A:int, T:tuple(int, int), D:int):int = A + T(0) + T(1) + D
H(A:int, (B:int, (C:int, D:int)), E:int):int = A + B + C + D + E
I(A:int, (B:int, (C:int, D:int)), E:int, (FF:int, GG:int, (HH:int, II:int))):int =
    A + B + C + D + E + FF + GG + HH + II
SumFour(A:int, (X:int, (Y:int, (Z:int)))):int = A + X + Y + Z
WithDefault((A:int, B:int), ?C:int = A * 10 + B):int = C
Swap((A:t, B:u) where t:type, u:type):tuple(u, t) = (B, A)
Apply((Fn(:int):int, X:int)):int = Fn(X)
Inc(X:int):int = X + 1
Both((A:int, B:int))<transacts>:int = A | B
Over(A:int, (B:int, C:int)):int = A + B + C
Over(A:int, B:string):int = A
box := class:
    K:int = 10
    Add((A:int, B:int), C:int):int = K + A + B + C
pt := class:
    X:int
    Y:int
MakePt<constructor>((A:int, B:int)) := pt:
    X := A
    Y := B
r := class:
    var N:int = 0
Fill(A:int, (B:tuple(int, int), C:int), R:r)<suspends>:void =
    Sleep(0.0)
    set R.N = A + B(0) + B(1) + C
Main()<suspends>:void =
    T := (2, 3)
    Print("{F(1, (2, 3), 4)} {F(1, T, 4)} {G(1, (2, 3), 4)} {G(1, T, 4)} {F((1, (2, 3), 4))}")
    T2 := (2, (3, 4))
    T3 := (1, (2, (3, 4)), 5)
    Print("{H(1, (2, (3, 4)), 5)} {H(1, T2, 5)} {H(T3)}")
    T4 := (1, (2, (3, 4)), 5, (6, 7, (8, 9)))
    T5 := (6, 7, (8, 9))
    Print("{I(1, (2, (3, 4)), 5, (6, 7, (8, 9)))} {I(T4)} {I(1, T2, 5, T5)}")
    Print("{SumFour(1, (2, (3, (4))))} {SumFour((1, (2, (3, (4)))))}")
    Print("{WithDefault((1, 2))} {WithDefault((1, 2), ?C := 7)}")
    P := Swap((1, "a"))
    Print("{P(0)} {P(1)} {Apply((Inc, 4))} {Over(1, (2, 3))} {Over(1, "s")}")
    for (V := Both((5, 6))) { Print("{V}") }
    Fv:type{_(:int, :tuple(int, int), :int):int} = F
    Own := F
    Print("{Fv(1, (2, 3), 4)} {Own(1, T, 4)} {box{}.Add((1, 2), 3)} {MakePt((7, 8)).Y}")
    R := r{}
    Task := spawn{Fill(1, ((2, 3), 4), R)}
    Task.Await()
    Print("{R.N}")
