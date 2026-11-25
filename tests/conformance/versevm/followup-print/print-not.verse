# A Print in the operand of `not`. The Book (ch. 6) says `not e` always
# discards e's effects, also when e succeeds (and `not` fails). Is the
# operand's line labelled "(Rolling Back)" in both cases, as
# followup/print-in-condition's was on the Verse VM (UEFN 43.12
# CL 60598086)? Read the raw log: tools/batch_loop.py strips the label.
# OpenVerse rolls the operand's output back either way and prints:
#   not succeeded | not failed | after
# If the Verse VM echoes a failed context's lines with the label:
#   (Rolling Back) operand fails | not succeeded |
#   (Rolling Back) operand succeeds | not failed | after
Noisy(Tag:string, Ok:logic)<decides><transacts>:void =
    Print("OVPROBE {Tag}")
    Ok?

Main():void =
    if (not Noisy["operand fails", false]):
        Print("OVPROBE not succeeded")
    if (not Noisy["operand succeeds", true]):
        Print("OVPROBE unexpected")
    else:
        Print("OVPROBE not failed")
    Print("OVPROBE after")
