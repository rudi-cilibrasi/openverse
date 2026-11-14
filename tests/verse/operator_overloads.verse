# A program's overloads of the operators +, -, * and / and of prefix -,
# operator'+'(L:t, R:u) and prefix'-'(X:t): an operator whose operands the
# built-in one does not take calls the program's overload the call fits (the
# Book of Verse's tests, Overloading.versetest 196-212,
# 2023-01-17-CharLiteralAsOperand). A <decides> one fails as its call does.
vec2i := struct{X:int, Y:int}
prefix'-'(V:vec2i):vec2i = vec2i{X := -V.X, Y := -V.Y}
operator'+'(L:vec2i, R:vec2i):vec2i = vec2i{X := L.X + R.X, Y := L.Y + R.Y}
operator'-'(L:vec2i, R:vec2i):vec2i = vec2i{X := L.X - R.X, Y := L.Y - R.Y}
operator'*'(L:vec2i, R:int):vec2i = vec2i{X := L.X * R, Y := L.Y * R}
operator'*'(L:int, R:vec2i):vec2i = vec2i{X := L * R.X, Y := L * R.Y}
operator'/'(L:vec2i, R:int)<transacts><decides>:vec2i =
    R <> 0
    vec2i{X := Floor(L.X / R), Y := Floor(L.Y / R)}
prefix'-'(C:char):char = C
operator'-'(L:char, R:char):char = L
Show(V:vec2i):string = "({V.X}, {V.Y})"
Main():void =
    A := vec2i{X := 1, Y := 2}
    B := vec2i{X := 5, Y := 6}
    Print("{Show(-A)} {Show(A + B)} {Show(A - B)} {Show(A * 3)} {Show(2 * B)}")
    if (Q := B / 2) then Print(Show(Q))
    if (not B / 0) then Print("no quotient")
    Print("{-3 + 4 * 2} {ToString(-'a')} {ToString('a' - 'b')}")
