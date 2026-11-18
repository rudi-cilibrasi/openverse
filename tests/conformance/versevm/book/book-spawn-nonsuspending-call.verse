# Book: Tests/Bugs/FORT-571286-CrashMisinterpretingUObjectPointerAsDynamicallyTypedValue.versetest:26
# (verse_vm_only): spawn of a call that does not suspend, whose argument does.
Produce()<suspends>:any = ()
Consume(:any):void = {}
Start():void = spawn{Consume(Produce())}

Main():void =
    Start()
    Print("OVPROBE spawned")
