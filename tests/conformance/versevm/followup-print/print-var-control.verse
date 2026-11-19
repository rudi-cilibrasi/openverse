# Control: a var write beside a Print in a condition that fails. The write
# must be rolled back on every reading; only the Print's line is in question
# (followup/print-in-condition, UEFN 43.12 CL 60598086, Verse VM, labelled it
# "(Rolling Back)"). Read the raw log: tools/batch_loop.py strips the label.
# OpenVerse rolls both back and prints:
#   count after 0
# If the Verse VM echoes a failed context's lines with the label:
#   (Rolling Back) count set to 5 | count after 0
Main():void =
    var Count:int = 0
    if (set Count = 5, Print("OVPROBE count set to {Count}"), false?):
        Print("OVPROBE unexpected")
    Print("OVPROBE count after {Count}")
