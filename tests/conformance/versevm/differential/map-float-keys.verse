# Map keys that are floats: 0.1 + 0.2 and 0.3, NaN, and a zero made
# negative.
# Tests LANGUAGE.md, float: "it has one NaN, which equals itself, and no
# negative zero"; Maps: a key is found by =. With IEEE equality a NaN key is
# never found again; with distinct negative zeros (and bitwise keys) -0.0
# would miss 0.0.
# OpenVerse prints (Lean and C agree):
#   -1 1 2 3 size 3
Main():void =
    Z:float = 0.0
    N:float = Z / Z
    var M:[float]int = map{0.3 => 1}
    if (set M[N] = 2, set M[-Z] = 3) {}
    A := M[0.1 + 0.2] or -1
    B := M[0.3] or -1
    C := M[N] or -1
    D := M[Z] or -1
    Print("OVPROBE {A} {B} {C} {D} size {M.Length}")
