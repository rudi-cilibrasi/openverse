# A Print in option{...} whose body fails, then one whose body succeeds.
# Is the failed body's line labelled "(Rolling Back)", as
# followup/print-in-condition's was on the Verse VM (UEFN 43.12
# CL 60598086)? Read the raw log: tools/batch_loop.py strips the label.
# OpenVerse rolls a failed body's output back and prints:
#   empty | inside 8 | some 8
# If the Verse VM echoes a failed context's lines with the label:
#   (Rolling Back) inside 2 | empty | inside 8 | some 8
Noisy(N:int)<decides><transacts>:int =
    Print("OVPROBE inside {N}")
    N > 5

Main():void =
    A:?int = option{Noisy[2]}
    if (V := A?):
        Print("OVPROBE some {V}")
    else:
        Print("OVPROBE empty")
    B:?int = option{Noisy[8]}
    if (W := B?):
        Print("OVPROBE some {W}")
    else:
        Print("OVPROBE empty")
