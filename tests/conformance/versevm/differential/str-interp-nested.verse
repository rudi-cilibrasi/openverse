# String literals inside an interpolation: a concatenation, a nested
# interpolation, and an empty string.
# Tests LANGUAGE.md, Literals: "strings with escapes and {expr}
# interpolation", any expression between the braces.
# OpenVerse prints (Lean and C agree):
#   a inner 7 xy 8
Main():void =
    I:int = 7
    Print("OVPROBE a {"in" + "ner"} {"{I}"} x{""}y {"{"{I + 1}"}"}")
