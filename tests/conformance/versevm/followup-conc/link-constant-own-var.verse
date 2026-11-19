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
Total:int = block:
    var Sum:int = 0
    for (I := 1..3):
        set Sum += I
    Sum

Main():void =
    Print("OVPROBE total {Total}")
