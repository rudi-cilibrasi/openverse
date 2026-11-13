# return near suspension points: in a for expression or statement whose body
# sleeps, and in an operand before a suspending call (#156, review of #158)
F(A:int)<suspends>:int =
    R := for (I := 0..1):
        if (A = I) then return 7
        Sleep(0.01)
        I
    R.Length
G(A:int)<suspends>:int =
    for (I := 0..1, J := 0..1):
        Sleep(0.01)
        if (A = I + J) then return 7
    0
H(A:int)<suspends>:int =
    Print("{(if (A > 0) then 1 else return 9) + Id(A)}")
    0
Id(X:int)<suspends>:int =
    Sleep(0.01)
    X
S(B:logic)<suspends>:string =
    if (B?):
        Sleep(0.01)
        return "early"
    Sleep(0.01)
    "late"
Main()<suspends>:void =
    Print("{F(1)} {F(5)}")
    Print("{G(1)} {G(5)}")
    Print("{H(1)} {H(-1)}")
    Print("{S(true)} {S(false)}")
