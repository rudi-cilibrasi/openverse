# Book: Tests/FunctionAsType.versetest:8 (verse_vm_only): a <closed> function
# used as a type.
IntString(X:int)<closed><computes>:string = "{X}"

Main():void =
    X:IntString = 1
    if (X = "1"):
        Print("OVPROBE converted")
    else:
        Print("OVPROBE not converted")
