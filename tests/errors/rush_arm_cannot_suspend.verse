# expect: this arm of rush cannot suspend
# Every arm of a rush can suspend (the Book's tests, Concurrency.versetest)
Wait()<suspends>:void =
    Sleep(1.0)
Main()<suspends>:void =
    rush:
        Wait()
        block:
            Print("at once")
