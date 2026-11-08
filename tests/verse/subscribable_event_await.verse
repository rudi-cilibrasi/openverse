# a subscribable_event is an event: awaited while a function is subscribed
# to it, which Signal calls before the waiter resumes (#210)
Main()<suspends>:void =
    E := subscribable_event(string){}
    S := E.Subscribe(Shout)
    race:
        block:
            V := E.Await()
            Print("awaited {V}")
        block:
            Sleep(0.1)
            E.Signal("go")
            Sleep(0.1)
    S.Cancel()
    E.Signal("quiet")
    Print("done")
Shout(S:string):void = Print("heard {S}")
