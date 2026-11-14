# A sticky_event's Signal resumes its awaiters inside it, in order; an
# awaiter that appears meanwhile, here one spawned by the first awaiter,
# returns at once (the Book's API, sticky_event's Signal: "Awaiters that
# appear during this drain ... return immediately, since the latch is now
# set")
Watch(Name:string, E:sticky_event(int))<suspends>:void =
    V := E.Await()
    Print("{Name} sees {V}")
Starter(E:sticky_event(int))<suspends>:void =
    V := E.Await()
    Print("starter sees {V}")
    spawn{Watch("late", E)}
    Print("starter goes on")
Main()<suspends>:void =
    E := sticky_event(int){}
    spawn{Starter(E)}
    spawn{Watch("early", E)}
    E.Signal(5)
    Print("main after signal")
