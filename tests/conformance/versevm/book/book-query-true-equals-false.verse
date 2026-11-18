# Book: Tests/Operators/BoolQuery.versetest:3 expects true? = false to
# succeed (the query's value is the empty value); docs/08_failure.md says a
# query of a value other than false succeeds with that value.
Check()<computes><decides>:void = true? = false

Main():void =
    if (Check[]):
        Print("OVPROBE query value equals false")
    else:
        Print("OVPROBE query value differs from false")
