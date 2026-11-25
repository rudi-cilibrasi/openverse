# Book: Tests/Bugs/SOL-4209-SuspendingSubexpressionsOfSpawnedInvocation.versetest:48
# (verse_vm_only): a spawned call whose argument suspends.
token := class {}
Use(:token)<suspends>:void = {}
Make()<suspends>:token = token{}
Start():void = spawn{Use(Make())}

Main():void =
    Start()
    Print("OVPROBE spawned")
