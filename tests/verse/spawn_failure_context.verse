# spawn in a failure context (the Book's tests: assertions spawn, and
# LiveVariables.versetest:450-545 spawn in a condition that fails): the
# task's start, its first run included, is the context's code; when the
# context fails it is undone, and the task never runs again
Worker(E:event(int))<suspends>:void =
    Print("worker starts")
    V := E.Await()
    Print("worker got {V}")
Start(E:event(int), Ok:logic)<decides><transacts>:void =
    spawn{Worker(E)}
    Ok?
Main():void =
    E := event(int){}
    if (Start[E, false]) then Print("started") else Print("not started")
    E.Signal(1)
    if (Start[E, true]) then Print("started") else Print("not started")
    E.Signal(2)
    Print("main ends")
