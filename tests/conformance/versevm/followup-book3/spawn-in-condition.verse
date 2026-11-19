# Edge of the spawn rule (#724): a spawn in an if's condition in Main. Epic
# refuses a spawn in a <transacts> function (3512, followup-book2);
# OpenVerse refuses it in a failure context too, as it refuses a call of a
# function without a heap specifier there ("this spawn has the 'no_rollback'
# effect, which a failure context does not allow"). If Epic admits it, it
# prints
#   spawned | before sleep | after sleep
# or without spawned.
Work()<suspends>:void =
    Print("OVPROBE spawned")

Main()<suspends>:void =
    Limit := 0
    if (T := spawn{Work()}, Limit > 0):
        Print("OVPROBE condition succeeded")
    Print("OVPROBE before sleep")
    Sleep(0.0)
    Print("OVPROBE after sleep")
