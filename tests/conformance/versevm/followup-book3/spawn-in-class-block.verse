# Edge of the spawn rule (#724): a spawn in a class's block:, which excludes
# no_rollback (the Book's Effects.versetest:551, 3512 for a call). OpenVerse
# refuses it. If Epic admits it, it prints
#   spawned | constructed | after sleep
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
