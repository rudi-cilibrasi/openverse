# expect: computing the constant Total allocates the var Sum declared in Total
# A var in the constant's own initialiser, and a constant called directly,
# not through a class's block: the same rule (OpenVerse's extrapolation; the
# Book's untagged GlobalVariables.versetest:79 has a direct call that
# allocates a var fail the link on both VMs; follow-up probe
# followup-conc/link-constant-own-var).
Total:int = block:
    var Sum:int = 0
    for (I := 1..3):
        set Sum += I
    Sum

Main():void =
    Print("{Total}")
