# A Print of a string with a newline in it, in a condition that fails. If
# the Verse VM echoes a failed context's lines with the "(Rolling Back)"
# label (followup/print-in-condition, UEFN 43.12 CL 60598086), does each
# line of the string get it, or only the first? Read the raw log: the second
# line carries no marker (batch mode tags only a literal's start), so the
# parser does not attribute it, and tools/batch_loop.py strips the label.
# OpenVerse rolls it back and prints:
#   after
# If the label is per Print call (one log entry of two lines):
#   (Rolling Back) first, then a bare line "second line" | after
Main():void =
    if (Print("OVPROBE first\nsecond line"), false?):
        Print("OVPROBE unexpected")
    Print("OVPROBE after")
