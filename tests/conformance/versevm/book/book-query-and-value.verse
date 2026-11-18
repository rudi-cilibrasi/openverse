# Book: Tests/Operators/LogicalAnd.versetest:29 expects (true? and true?) =
# false to succeed; docs/08_failure.md gives a query the value it queried.
Check()<computes><decides>:void = (true? and true?) = false

Main():void =
    if (Check[]):
        Print("OVPROBE and value equals false")
    else:
        Print("OVPROBE and value differs from false")
