# Book: Tests/Coroutines/SpawnAndTask.versetest:1030 (verse_vm_only): a spawn
# block of several expressions inside a loop.
Main():void =
    var Z:int = 0
    var X:int = 0
    Event := event(){}
    loop:
        Y := X
        if (Y >= 3):
            break
        spawn:
            Event.Await()
            set Z += Y
        set X += 1
    Event.Signal()
    Print("OVPROBE sum {Z}")
