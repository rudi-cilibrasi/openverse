# A Print in the left operand of `or`, which fails once and succeeds once.
# The left of `or` is a failure context (Book ch. 6): is a failed left's line
# labelled "(Rolling Back)", as followup/print-in-condition's was on the
# Verse VM (UEFN 43.12 CL 60598086)? Read the raw log: tools/batch_loop.py
# strips the label.
# OpenVerse rolls a failed left's output back and prints:
#   result 42 | left 9 | result 9
# If the Verse VM echoes a failed context's lines with the label:
#   (Rolling Back) left 1 | result 42 | left 9 | result 9
Noisy(N:int)<decides><transacts>:int =
    Print("OVPROBE left {N}")
    N > 5

Main():void =
    X := Noisy[1] or 42
    Print("OVPROBE result {X}")
    Y := Noisy[9] or 0
    Print("OVPROBE result {Y}")
