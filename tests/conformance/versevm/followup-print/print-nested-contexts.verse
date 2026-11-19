# Prints in nested failure contexts. First an inner condition fails inside an
# outer condition that succeeds; then a line printed by a call that succeeded
# belongs to an outer condition that fails. followup/print-in-condition (UEFN
# 43.12 CL 60598086, Verse VM) labelled a failed condition's line
# "(Rolling Back)". Which lines get the label here, once or twice, and in what
# order (a rolled-back inner line before the outer line printed earlier would
# mean committed lines wait for the outermost commit)? Read the raw log:
# tools/batch_loop.py strips the label.
# OpenVerse rolls output back with each failed context and prints:
#   outer one | end one | one passed | after
# If the Verse VM echoes a failed context's lines once, in program order:
#   outer one | (Rolling Back) inner one | end one | one passed |
#   (Rolling Back) outer two | (Rolling Back) inner two |
#   (Rolling Back) end two | after
Noisy(Tag:string, Ok:logic)<decides><transacts>:void =
    Print("OVPROBE {Tag}")
    Ok?

Inner(Tag:string)<transacts>:void =
    if (Noisy[Tag, false]):
        Print("OVPROBE unexpected inner")

Main():void =
    if (Print("OVPROBE outer one"), Inner("inner one"), Noisy["end one", true]):
        Print("OVPROBE one passed")
    if (Print("OVPROBE outer two"), Noisy["inner two", true], Noisy["end two", false]):
        Print("OVPROBE unexpected")
    Print("OVPROBE after")
