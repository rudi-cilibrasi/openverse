# Edge of the spawn rule (#724): a spawn in an if's condition in Main. Epic
# refuses a spawn in a <transacts> function (3512, followup-book2);
# OpenVerse refuses it in a failure context too, as it refuses a call of a
# function without a heap specifier there ("this spawn has the 'no_rollback'
# effect, which a failure context does not allow"). If Epic admits it, it
# prints
#   spawned | before sleep | after sleep
# or without spawned.
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3512 (L13) "This 'spawn' macro has the
# 'no_rollback' effect, which is not allowed by its context."; 3512 (L13)
# "This invocation calls a function (`(<project>:)Work`) that has the
# 'no_rollback' effect, which is not allowed by its con".
Work()<suspends>:void =
    Print("OVPROBE spawned")

Main()<suspends>:void =
    Limit := 0
    if (T := spawn{Work()}, Limit > 0):
        Print("OVPROBE condition succeeded")
    Print("OVPROBE before sleep")
    Sleep(0.0)
    Print("OVPROBE after sleep")
