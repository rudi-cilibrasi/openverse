# Operators defined by the program for a struct, + and *, in one expression:
# the precedence of the built-in operators kept.
# Tests LANGUAGE.md, Overloading (operators the program defines, as
# operator'+'); the Book's ch. 4 precedence for the overloaded operators.
# OpenVerse prints (Lean and C agree):
#   21 42 32 64
vec2 := struct:
    X:int
    Y:int

operator'+'(A:vec2, B:vec2):vec2 = vec2{X := A.X + B.X, Y := A.Y + B.Y}
operator'*'(A:vec2, K:int):vec2 = vec2{X := A.X * K, Y := A.Y * K}

Main():void =
    A := vec2{X := 1, Y := 2}
    B := vec2{X := 10, Y := 20}
    C := A + B * 2
    D := B * 3 + A + A
    Print("OVPROBE {C.X} {C.Y} {D.X} {D.Y}")
