# followup-corners (#724): A rational compared with an int by <: 1 / 2 < 1.
# Compile only. Expected: refused by Epic (3509), which refused two
# rationals (differential/rat-ordering, a probe that also had an int).
# OpenVerse (Lean and C agreeing): refused, '<' does not order a rational
# (3509).
# If Epic refuses it (3509), OpenVerse agrees. If it admits it and prints
# less y, < takes a rational and an int though not two rationals: OpenVerse
# would admit that pair.
# Not yet compiled or run by UEFN.
Main():void =
    A := if (1 / 2 < 1) then "y" else "n"
    Print("OVPROBE less {A}")
