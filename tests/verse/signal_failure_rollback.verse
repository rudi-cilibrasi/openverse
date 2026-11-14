# A Signal in a failure context resumes its awaiters inside it; when the
# context fails, what they did is undone with it, and the awaiter waits
# again where it waited (the Book's tests: Event.versetest signals in
# <decides> functions; Coroutines/Concurrency.versetest:1562-1580)
count := class:
    var N:int = 0
Bump(C:count, E:event(int))<suspends>:void =
    loop:
        V := E.Await()
        set C.N += V
        Print("bumped by {V}")
Try(C:count, E:event(int), X:int)<decides><transacts>:void =
    E.Signal(X)
    C.N < 10
Main():void =
    C := count{}
    E := event(int){}
    spawn{Bump(C, E)}
    if (Try[C, E, 3]) then Print("kept {C.N}") else Print("undone {C.N}")
    if (Try[C, E, 20]) then Print("kept {C.N}") else Print("undone {C.N}")
    E.Signal(1)
    Print("final {C.N}")
