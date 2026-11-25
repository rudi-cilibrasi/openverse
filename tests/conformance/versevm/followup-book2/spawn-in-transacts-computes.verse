# Book: Tests/Effects.versetest:557 (bp_vm_only): spawn of a
# <computes><suspends> function in a <transacts> function. The Book's
# Blueprint VM refuses it, 3512 ("spawn requires the transacts effect in
# addition to the effects of the spawned async function"; a function without
# specifiers may spawn); the Verse VM twin (:572) is valid and agrees in
# OpenVerse, which prints
#   started | after sleep
# If UEFN 43.12 refuses it, its front end applies the Blueprint VM's rule
# whatever the VM: a spawn needs a function without heap specifiers, as an
# event's Signal does (3512). Control: spawn-in-transacts-computes-control
# (the Book's :556 and :571).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3512 (L13) "This 'spawn' macro has the
# 'no_rollback' effect, which is not allowed by its context.".
Work()<computes><suspends>:void = {}

Start()<transacts>:void = spawn{Work()}

Main()<suspends>:void =
    Start()
    Print("OVPROBE started")
    Sleep(0.0)
    Print("OVPROBE after sleep")
