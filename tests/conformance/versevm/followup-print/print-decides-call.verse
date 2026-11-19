# A Print inside a <decides><transacts> function whose call fails in an if
# condition. followup/print-in-condition (UEFN 43.12 CL 60598086, Verse VM)
# logged its condition's line with the label "(Rolling Back)" before the
# marker: is a callee's line in a failed condition labelled the same way?
# Read the raw log: tools/batch_loop.py strips the "(Rolling Back) " label.
# OpenVerse rolls output back with the condition and prints:
#   checking 7 | seven passed | after
# If the Verse VM echoes a failed context's lines with the label:
#   (Rolling Back) checking 3 | checking 7 | seven passed | after
Check(N:int)<decides><transacts>:void =
    Print("OVPROBE checking {N}")
    N > 5

Main():void =
    if (Check[3]):
        Print("OVPROBE unexpected")
    if (Check[7]):
        Print("OVPROBE seven passed")
    Print("OVPROBE after")
