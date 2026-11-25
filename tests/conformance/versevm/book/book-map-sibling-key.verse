# Book: Tests/Map.versetest:363 (verse_vm_only): a map keyed by one subclass,
# written through a key of a sibling subclass, compiles and fails.
key_base := class<unique> {}
key_a := class(key_base) {}
key_b := class(key_base) {}
entry := class<unique>:
    var Data:int = 0

Main():void =
    var X:[key_a]entry = map{}
    Key := key_a{}
    Value := entry{}
    if (set X[Key] = Value, X[Key] = Value):
        Print("OVPROBE inserted")
    if (set X[key_b{}].Data = 1):
        Print("OVPROBE sibling key write succeeded")
    else:
        Print("OVPROBE sibling key write failed")
