# Edge of the spawn rule (#724): a spawn in a class's block:, which excludes
# no_rollback (the Book's Effects.versetest:551, 3512 for a call). OpenVerse
# refuses it. If Epic admits it, it prints
#   spawned | constructed | after sleep
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3512 (L9) "This 'spawn' macro has the
# 'no_rollback' effect, which is not allowed by its context."; 3512 (L9)
# "This invocation calls a function (`(<project>:)Work`) that has the
# 'no_rollback' effect, which is not allowed by its con".
Work()<suspends>:void =
    Print("OVPROBE spawned")

holder := class:
    block:
        spawn{Work()}

Main()<suspends>:void =
    H := holder{}
    Print("OVPROBE constructed")
    Sleep(0.0)
    Print("OVPROBE after sleep")
