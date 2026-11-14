# a subscribable_event is an event: awaited while a function is subscribed
# to it, which Signal calls after the waiter, resumed inside it, waits again
# or ends (#210; the Book's API: "Subscribers ... are invoked only after
# every waiting task has been resumed")
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
