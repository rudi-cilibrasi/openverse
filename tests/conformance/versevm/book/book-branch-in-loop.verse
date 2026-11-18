# Book: Tests/FlowControl/Concurrency/branch.versetest:183 (verse_vm_only): a
# branch inside a loop.
int_ref := class:
    var Contents:int = 0

Fill(Result:int_ref)<suspends>:void =
    Event := event(){}
    var X:int = 0
    loop:
        Y := X
        if (Y >= 3):
            break
        branch:
            Event.Await()
            set Result.Contents += Y
        set X += 1
    Event.Signal()

Main():void =
    R := int_ref{}
    spawn{Fill(R)}
    Print("OVPROBE contents {R.Contents}")
