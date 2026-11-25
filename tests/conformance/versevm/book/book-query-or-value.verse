# Book: Tests/Operators/Precedence.versetest:121 expects x := true? or true
# to bind the empty value (x = false succeeds); :122 gives x := false? or true
# the value true.
Check()<computes><decides>:void =
    x := true? or true
    x = false

Main():void =
    if (Check[]):
        Print("OVPROBE or value equals false")
    else:
        Print("OVPROBE or value differs from false")
