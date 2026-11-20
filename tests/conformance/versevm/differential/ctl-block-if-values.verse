# The values of blocks and if expressions: a block's last expression, if
# with else as a value, nested ifs, and a block's local names.
# Tests LANGUAGE.md, Supported, Blocks: "block:", "a value after = ... that
# starts a later line, deeper, is the indented block of those lines";
# Control: if/else if/else.
# OpenVerse prints (Lean and C agree):
#   9 4 four 2
Main():void =
    A:int = block:
        X := 3
        X * X
    B := if (A > 5) then A - 5 else A + 5
    C:string =
        if (B = 4):
            "four"
        else if (B = 5):
            "five"
        else:
            "other"
    D := if (A < 0) then 1 else if (A < 10) then 2 else 3
    Print("OVPROBE {A} {B} {C} {D}")
