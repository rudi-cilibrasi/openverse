# A chain of calls of the program's own method named Signal, Cancel, Await
# or Subscribe, each on the result of the call before it (#773). Those are
# the names of the methods of events and tasks, so a call of one asks first
# whether its receiver is an event, a task or a value of a type parameter
# that has the method. Each of those questions elaborated the receiver for
# itself, and the call elaborated it again: three elaborations at each call
# of Signal(), Cancel() and Await(), two at Subscribe(F), each making as
# many of the call before, so twelve calls took ten seconds to compile and
# the forty of the first chain here would not end. The receiver is
# elaborated once now.
# Each call of `trail` appends a letter that says which method took it: `s`
# for Signal, `c` for Cancel, `a` for Await and the number given for
# Subscribe, so a chain prints its calls in the order they are made. Beside
# them, the events' and tasks' own methods of the same names, which the
# same code tells apart from the receiver's type.
trail := class:
    T:string = ""
    Signal():trail = trail{T := "{T}s"}
    Cancel():trail = trail{T := "{T}c"}
    Await():trail = trail{T := "{T}a"}
    Subscribe(N:int):trail = trail{T := "{T}{N}"}
# (each fails once the trail is as long as `Most`)
strict := class:
    T:string = ""
    Most:int
    Signal()<decides><transacts>:strict =
        T.Length < Most
        strict{T := "{T}s", Most := Most}
    Cancel()<decides><transacts>:strict =
        T.Length < Most
        strict{T := "{T}c", Most := Most}
    Await()<decides><transacts>:strict =
        T.Length < Most
        strict{T := "{T}a", Most := Most}
# (each waits before it answers)
slow := class:
    T:string = ""
    Signal()<suspends>:slow =
        Sleep(0.0)
        slow{T := "{T}s"}
    Cancel()<suspends>:slow =
        Sleep(0.0)
        slow{T := "{T}c"}
    Await()<suspends>:slow =
        Sleep(0.0)
        slow{T := "{T}a"}
# (its own Signal and Await beside those of the event and the task it holds)
holder := class:
    Ev:event()
    Job:task(string)
    Signal():holder =
        Print("holder.Signal")
        Self
    Await():holder =
        Print("holder.Await")
        Self
Try(S:strict):string =
    if (Y := S.Await[].Signal[].Cancel[].Await[].Cancel[].Await[].Signal[].Cancel[].Signal[].Cancel[].Await[].Signal[].Await[].Signal[].Cancel[].Await[].Cancel[].Await[].Signal[].Cancel[].Signal[].Cancel[].Await[].Signal[].Await[].Signal[].Cancel[].Await[].Cancel[].Await[]):
        Y.T
    else:
        "failed"
On():void = Print("subscribed function called")
Slowly(S:slow)<suspends>:string = S.Await().Cancel().Signal().Await().Cancel().Await().Cancel().Signal().Await().Cancel().Await().Cancel().T
Waiter(E:event())<suspends>:void =
    E.Await()
    Print("waiter resumed")
Sender(G:event(int))<suspends>:void =
    Sleep(0.0)
    G.Signal(41)
Sleeper()<suspends>:void =
    defer:
        Print("sleeper cancelled")
    Sleep(100.0)
    Print("sleeper woke (wrong)")
Main()<suspends>:void =
    X := trail{}
    Print(X.Signal().Cancel().Signal().Await().Cancel().Await().Await().Subscribe(7).Await().Signal().Subscribe(0).Signal().Signal().Cancel().Signal().Await().Cancel().Await().Await().Subscribe(9).Await().Signal().Subscribe(2).Signal().Signal().Cancel().Signal().Await().Cancel().Await().Await().Subscribe(1).Await().Signal().Subscribe(4).Signal().Signal().Cancel().Signal().Await().T)
    Print(Try(strict{Most := 1000}))
    Print(Try(strict{Most := 17}))
    # a task's Await, of a task that makes a chain of calls that wait
    Job := spawn{Slowly(slow{})}
    Print(Job.Await())
    # an event's Subscribe and Signal, and a subscription's Cancel
    E := event(){}
    S := E.Subscribe(On)
    E.Signal()
    S.Cancel()
    E.Signal()
    # an event's Await and Signal, with a value and without
    G := event(int){}
    spawn{Sender(G)}
    Print("got {G.Await()}")
    W := spawn{Waiter(E)}
    E.Signal()
    W.Await()
    # a task's Cancel
    L := spawn{Sleeper()}
    L.Cancel()
    # the program's Signal and Await, then the event's and the task's
    H := holder{Ev := E, Job := Job}
    V := E.Subscribe(On)
    H.Signal().Await().Signal().Ev.Signal()
    Print(H.Await().Signal().Await().Job.Await())
    V.Cancel()
    Print("done")
