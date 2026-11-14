# A task's end resumes its awaiters inside its last step, before the
# scheduler runs any other task (the Book's API, task, Await; the tests'
# mechanism, Bugs/FORT-1088027-UseOfNullInitializedDynamicallyTypedValue
# .versetest:6-9, "event::Signal → task::Complete → ResumeAt →
# task::Update"): Work, w1, Other and w2 all wake at one tick; Work's end
# resumes w1, w2 and Main, which registered in that order, before Other.
Work()<suspends>:int =
    Sleep(0.1)
    Print("work ends")
    5
Other()<suspends>:void =
    Sleep(0.1)
    Print("other wakes")
Waiter(T:task(int), N:string)<suspends>:void =
    Print("{N} got {T.Await()}")
    Sleep(0.1)
    Print("{N} later")
Main()<suspends>:void =
    T := spawn{Work()}
    spawn{Waiter(T, "w1")}
    spawn{Other()}
    spawn{Waiter(T, "w2")}
    Print("main got {T.Await()}")
    Sleep(0.5)
