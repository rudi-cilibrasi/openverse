# Book: Tests/Definitions.versetest:37;
# Tests/Attributes/CustomClassVarAccessors.versetest:642 (2 cases): a
# definition used as an expression, X:int = Y:int = 4, both names bound after
# it. The Book's tests expect them valid.
# OpenVerse (ce8632ea, Lean) refused this probe: "unknown identifier 'Y'"
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-20) admitted it and printed
#   x 4 y 4
# OpenVerse now prints it too (#724, Lean and C): a definition whose value
# is a definition defines both in its scope (tests/verse/definition_chain).
Main():void =
    X:int = Y:int = 4
    Print("OVPROBE x {X} y {Y}")
