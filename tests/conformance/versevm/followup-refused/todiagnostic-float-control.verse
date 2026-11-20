# Control of todiagnostic-float: ToDiagnostic of an int, which OpenVerse
# admits. Not a Book case.
# OpenVerse (ce8632ea, Lean and C agreeing) prints
#   diagnostic 15
# If UEFN 43.12 refuses this too, todiagnostic-float's refusal is not the
# form's.
# The Book's API reference marks diagnostic's String <epic_internal>: if UEFN
# 43.12 refuses this (3593, as it refused task's Cancel,
# followup-conc/cancel-task-child), OpenVerse admits a program Epic refuses,
# and the 14 float cases are refused by Epic for String, not for the float.
Main():void =
    D := ToDiagnostic(15)
    Print("OVPROBE diagnostic {D.String}")
