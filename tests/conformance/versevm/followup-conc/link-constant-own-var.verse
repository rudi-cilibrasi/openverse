# A module constant whose own initialiser declares a var (no class block, no
# function call). Epic's Verse VM fails the session's cook with 9003 when a
# module constant's class block allocates a var (book-global-block-*, UEFN
# 43.12); OpenVerse extrapolates the rule to any var the computation of a
# module constant allocates, and refuses this program before it runs:
#   "computing the constant Total allocates the var Sum declared in Total"
# If the Verse VM only checks what the blocks of module-level instances do,
# it links and prints:
#   total 6
# (Run it alone, not in a batch: a cook failure stops the whole session.)
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-19) refuses it at compile time: 3512 "This mutable data definition has
# the 'allocates' effect, which is not allowed by its context" (the var),
# 3582 "Expressions with side effects cannot be used when defining
# data-members" and 3582 "Divergent calls (calls that might not complete)
# cannot be used to define data-members" (the for), 3512 "This mutable data
# read has the 'reads' effect, which is not allowed by its context" (Sum).
# OpenVerse refuses it too, with its own message, before it runs.
Total:int = block:
    var Sum:int = 0
    for (I := 1..3):
        set Sum += I
    Sum

Main():void =
    Print("OVPROBE total {Total}")
