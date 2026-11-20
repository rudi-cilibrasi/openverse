# Floor, Ceil, Round and Int fail on NaN and the infinities.
# Tests LANGUAGE.md, float: "They fail on NaN or an infinity"; Epic's digest:
# "Fails if not IsFinite(Val)". (At the edges of the 64-bit range:
# float-round-edges, run alone.)
# OpenVerse prints (Lean and C agree):
#   specials floor-nan fails ceil-inf fails round-neginf fails int-nan fails
Main():void =
    Z:float = 0.0
    N:float = Z / Z
    A := if (Floor[N]) then "ok" else "fails"
    B := if (Ceil[Inf]) then "ok" else "fails"
    C := if (Round[-Inf]) then "ok" else "fails"
    D := if (Int[N]) then "ok" else "fails"
    Print("OVPROBE specials floor-nan {A} ceil-inf {B} round-neginf {C} int-nan {D}")
