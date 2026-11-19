# Book: Tests/Effects.versetest:565 (bp_vm_only): spawn of a
# <transacts><suspends> function in a <transacts> function. The Book's
# Blueprint VM refuses it, 3512; the Verse VM twin (:580) is valid and
# agrees in OpenVerse, which starts the task at once and prints
#   spawned ran | started | after sleep
# If the spawned task first runs at the next yield: started | spawned ran |
# after sleep. If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of
# a Verse VM session), Epic's shipped toolchain refuses a program OpenVerse
# runs. Control: spawn-in-transacts-computes-control.
Work()<transacts><suspends>:void =
    Print("OVPROBE spawned ran")

Start()<transacts>:void = spawn{Work()}

Main()<suspends>:void =
    Start()
    Print("OVPROBE started")
    Sleep(0.0)
    Print("OVPROBE after sleep")
