# Control of spawn-in-transacts-computes: the same spawn in a function
# without specifiers. Book: Tests/Effects.versetest:556 (bp_vm_only) and
# :571 (verse_vm_only), both valid. OpenVerse prints
#   started | after sleep
Work()<computes><suspends>:void = {}

Start():void = spawn{Work()}

Main()<suspends>:void =
    Start()
    Print("OVPROBE started")
    Sleep(0.0)
    Print("OVPROBE after sleep")
