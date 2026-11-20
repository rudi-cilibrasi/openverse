# Book: Tests/Intrinsics/ToDiagnostic.versetest 75, 76, 78, 79, 81, 82, 83,
# 84, 87, 125, 134, 142, 143, 144 (14 cases): ToDiagnostic of a float, read
# through the diagnostic's String (the Book's API reference declares
# ToDiagnostic <public> and diagnostic's String <epic_internal>). The Book's
# tests expect them valid.
# OpenVerse (ce8632ea, Lean) refuses this probe: "ToDiagnostic of a float (the
# shortest decimal that reads back is a Verse Core primitive not written yet)
# is not supported yet: a value of type float is converted to any in a program
# that calls ToDiagnostic"
# If UEFN 43.12 admits it, it prints
#   diagnostic 1.5
# and OpenVerse has a gap on Verse that Epic ships; if it refuses it, the Book
# is ahead of the shipped compiler here and OpenVerse's refusal is Epic's.
# Control: todiagnostic-float-control (ToDiagnostic of an int, which OpenVerse
# admits).
Main():void =
    D := ToDiagnostic(1.5)
    Print("OVPROBE diagnostic {D.String}")
