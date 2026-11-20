# ToString of infinities and NaN, made by arithmetic and by the constant Inf.
# Tests LANGUAGE.md, Readings, "ToString of a float": "Inf, -Inf, NaN";
# float: "Dividing by zero gives Inf, -Inf or NaN; it does not fail". The
# API names them Inf, -Inf and NaN; a C formatter would give inf and nan
# (and -nan for the x86 default NaN, which has its sign bit set).
# OpenVerse prints (Lean and C agree):
#   div Inf -Inf NaN NaN | inf Inf -Inf NaN NaN Inf Inf
#   overflow Inf -Inf Inf
Main():void =
    Z:float = 0.0
    Print("OVPROBE div {1.0 / Z} {-1.0 / Z} {Z / Z} {-Z / Z}")
    Print("OVPROBE inf {Inf} {-Inf} {Inf - Inf} {Inf * Z} {Inf + Inf} {-Inf * -1.0}")
    Big:float = 1.0e308
    Print("OVPROBE overflow {Big * 10.0} {-Big * 10.0} {Big + Big}")
