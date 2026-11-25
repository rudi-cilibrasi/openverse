# Control: a Print in a condition that succeeds. Its line must be logged
# without the "(Rolling Back)" label that followup/print-in-condition's
# failed condition got on the Verse VM (UEFN 43.12 CL 60598086), else the
# label would not mean "rolled back". Read the raw log: tools/batch_loop.py
# strips the label.
# OpenVerse prints:
#   in passing condition | then branch | after
# The Verse VM is expected to print the same, with no label.
Main():void =
    Limit:int = 3
    if (Print("OVPROBE in passing condition"), Limit > 1):
        Print("OVPROBE then branch")
    Print("OVPROBE after")
