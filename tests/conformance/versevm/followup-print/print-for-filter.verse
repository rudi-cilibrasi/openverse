# A Print in a for filter that fails for some elements. Is each rejected
# element's line labelled "(Rolling Back)" (as followup/print-in-condition's
# was on the Verse VM, UEFN 43.12 CL 60598086), and is it logged before the
# next element's lines? Read the raw log: tools/batch_loop.py strips the label.
# OpenVerse rolls a failed filter's output back and prints:
#   filter 1 | body 1 | filter 3 | body 3 | after
# If the Verse VM echoes a failed context's lines with the label:
#   filter 1 | body 1 | (Rolling Back) filter 2 | filter 3 | body 3 |
#   (Rolling Back) filter 4 | after
Odd(I:int)<decides><transacts>:int =
    Print("OVPROBE filter {I}")
    Mod[I, 2] = 1
    I

Main():void =
    for (I := 1..4, J := Odd[I]):
        Print("OVPROBE body {J}")
    Print("OVPROBE after")
