# A Print whose string interpolates a call that prints, in a condition that
# fails. followup/print-in-condition (UEFN 43.12 CL 60598086, Verse VM)
# labelled a failed condition's line "(Rolling Back)": are both lines
# labelled, the callee's first? Read the raw log: tools/batch_loop.py strips
# the label.
# OpenVerse rolls both back and prints:
#   after
# If the Verse VM echoes a failed context's lines with the label:
#   (Rolling Back) computing 4 | (Rolling Back) value 4 | after
Tell(N:int)<transacts>:int =
    Print("OVPROBE computing {N}")
    N

Main():void =
    if (Print("OVPROBE value {Tell(4)}"), false?):
        Print("OVPROBE unexpected")
    Print("OVPROBE after")
