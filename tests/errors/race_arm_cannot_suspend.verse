# expect: this arm of race cannot suspend
# Every arm of a race can suspend (the Book's tests, Concurrency.versetest:
# "Ensure all top-level expressions in race/rush are async")
Wait()<suspends>:int =
    Sleep(1.0)
    1
Now():int = 2
Main()<suspends>:void =
    X := race:
        Wait()
        Now()
    Print("{X}")
