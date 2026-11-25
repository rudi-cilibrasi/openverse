# followup-corners (#724): = beside an ordering comparison in one chain: 1 <
# 2 = 2 and 2 = 2 < 1.
# OpenVerse (Lean and C agreeing): ran, equal y n (every adjacent pair: 1 <
# 2 and 2 = 2; 2 = 2 and 2 < 1).
# If Epic prints equal y n, OpenVerse agrees. equal n n would mean = after <
# compares the left operand of what is before it, (1 < 2) = 2 being 1 = 2,
# as < after > does. A refusal (3100 or 3509) would mean the forms do not
# mix: OpenVerse would refuse them.
# Not yet compiled or run by UEFN.
Main():void =
    A := if (1 < 2 = 2) then "y" else "n"
    B := if (2 = 2 < 1) then "y" else "n"
    Print("OVPROBE equal {A} {B}")
