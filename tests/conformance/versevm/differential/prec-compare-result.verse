# The value of a successful comparison: the left operand, used as an int.
# Tests LANGUAGE.md, Readings, "X = Y result": "the operators page says
# logic; elsewhere the left operand (§5.4)"; openverse: "the left operand"
# (the Book's tests: CompareTypeChecking.versetest:8, CompareMap.versetest:19).
# Epic's compiler refuses this probe if a comparison's value is a logic.
# OpenVerse prints (Lean and C agree):
#   8 14 -3 2
Main():void =
    X:int = 7
    A := if (V := (X = 7)) then V + 1 else -1
    B := if (V := (X > 3)) then V * 2 else -1
    C := if (V := (X <> 4)) then V - 10 else -1
    S:string = "ab"
    D := if (T := (S = "ab")) then T.Length else -1
    Print("OVPROBE {A} {B} {C} {D}")
