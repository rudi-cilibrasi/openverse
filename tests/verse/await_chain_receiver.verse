# An event's and a task's own Await, Signal, Subscribe and Cancel (#775). A
# call `X.Await()` is an event's or a task's when `X` is one, so `X` is
# elaborated to see what it is, and the call then becomes a call of a helper
# with `X` as its argument, `$Await(X)`, `$EvAwait(X)`, `$StickyAwait(X)`,
# `$subscribeUnit(X, F)`, or of `X.Signal(())`. That elaborated `X` a second
# time, so a chain `E.Await().Await()…` over an event of events, or a task
# of tasks, took twice as long for each call in it: fourteen took five
# seconds to compile. The helper takes the receiver as it is elaborated now.
# First, receivers with effects: `Pick` prints and counts each time it is
# called, and each receiver is to be evaluated once, before what the call
# does. Then receivers that the type the call is to give makes another: of
# `A:animal = Wrap(dog{}).Await()` the helper is asked for an animal, so its
# argument is elaborated as an event of animals, which makes `Wrap`'s `t`
# animal; as elaborated alone it is an event of dogs, which is no event of
# animals, so it is elaborated at that type as before. Then the chains,
# sixteen deep, each level waking the next.
counter := class:
    var N:int = 0
box := class:
    Ev:event()
    Num:event(int)
    Stick:sticky_event(int)
    Sub:subscribable_event()
    Deep:event(event(int))
    Job:task(int)
    Long:task(int)
Pick(Name:string, C:counter, B:box):box =
    set C.N += 1
    Print("receiver of {Name}")
    B
Worker()<suspends>:int =
    Sleep(0.0)
    5
Sleeper()<suspends>:int =
    defer:
        Print("sleeper cancelled")
    Sleep(100.0)
    Print("sleeper woke (wrong)")
    0
On():void = Print("subscriber called")
SendUnit(E:event())<suspends>:void =
    Sleep(0.0)
    Print("signalling event()")
    E.Signal()
SendDeep(E:event(event(int)))<suspends>:void =
    Sleep(0.0)
    I := event(int){}
    spawn{Send1(I)}
    E.Signal(I)
animal := class:
    Name:string = "animal"
dog := class(animal):
    Name<override>:string = "dog"
Wrap(X:t where t:type):event(t) =
    E := event(t){}
    spawn{Send(E, X)}
    E
Send(E:event(t), X:t where t:type)<suspends>:void =
    Sleep(0.0)
    E.Signal(X)
Kept(X:t where t:type):sticky_event(t) =
    E := sticky_event(t){}
    E.Signal(X)
    E
Later(X:t where t:type)<suspends>:t =
    Sleep(0.0)
    X
Start(X:t where t:type)<suspends>:task(t) = spawn{Later(X)}
Show(A:animal):void = Print("shown a {A.Name}")
Hinted()<suspends>:void =
    A:animal = Wrap(dog{}).Await()
    Print("an event's {A.Name}")
    B:animal = Kept(dog{}).Await()
    Print("a sticky event's {B.Name}")
    D:animal = Start(dog{}).Await()
    Print("a task's {D.Name}")
    Show(Wrap(dog{}).Await())
    Show(Start(dog{}).Await())
    L:[]animal = array{Wrap(dog{}).Await(), animal{}}
    Print("{L.Length} animals")
Effects()<suspends>:void =
    C := counter{}
    B := box{Ev := event(){}, Num := event(int){}, Stick := sticky_event(int){}, Sub := subscribable_event(){}, Deep := event(event(int)){}, Job := spawn{Worker()}, Long := spawn{Sleeper()}}
    S := Pick("Subscribe", C, B).Ev.Subscribe(On)
    Pick("Signal", C, B).Ev.Signal()
    S.Cancel()
    spawn{SendUnit(B.Ev)}
    Pick("Await of an event()", C, B).Ev.Await()
    Print("event() awaited")
    spawn{Send1(B.Num)}
    V := Pick("Await of an event(int)", C, B).Num.Await()
    Print("event(int) gave {V}")
    B.Stick.Signal(9)
    W := Pick("Await of a sticky_event(int)", C, B).Stick.Await()
    Print("sticky_event(int) gave {W}")
    U := Pick("Subscribe of a subscribable_event()", C, B).Sub.Subscribe(On)
    Pick("Signal of a subscribable_event()", C, B).Sub.Signal()
    U.Cancel()
    B.Sub.Signal()
    spawn{SendDeep(B.Deep)}
    D := Pick("a chain of two Await", C, B).Deep.Await().Await()
    Print("the chain gave {D}")
    J := Pick("Await of a task", C, B).Job.Await()
    Print("task gave {J}")
    Pick("Cancel of a task", C, B).Long.Cancel()
    Print("receivers evaluated: {C.N}")
Send1(E:event(int))<suspends>:void =
    Sleep(0.0)
    E.Signal(7)
Send2(E:event(event(int)))<suspends>:void =
    Sleep(0.0)
    I := event(int){}
    spawn{Send1(I)}
    E.Signal(I)
Send3(E:event(event(event(int))))<suspends>:void =
    Sleep(0.0)
    I := event(event(int)){}
    spawn{Send2(I)}
    E.Signal(I)
Send4(E:event(event(event(event(int)))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(int))){}
    spawn{Send3(I)}
    E.Signal(I)
Send5(E:event(event(event(event(event(int))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(int)))){}
    spawn{Send4(I)}
    E.Signal(I)
Send6(E:event(event(event(event(event(event(int)))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(int))))){}
    spawn{Send5(I)}
    E.Signal(I)
Send7(E:event(event(event(event(event(event(event(int))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(int)))))){}
    spawn{Send6(I)}
    E.Signal(I)
Send8(E:event(event(event(event(event(event(event(event(int)))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(event(int))))))){}
    spawn{Send7(I)}
    E.Signal(I)
Send9(E:event(event(event(event(event(event(event(event(event(int))))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(event(event(int)))))))){}
    spawn{Send8(I)}
    E.Signal(I)
Send10(E:event(event(event(event(event(event(event(event(event(event(int)))))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(event(event(event(int))))))))){}
    spawn{Send9(I)}
    E.Signal(I)
Send11(E:event(event(event(event(event(event(event(event(event(event(event(int))))))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(event(event(event(event(int)))))))))){}
    spawn{Send10(I)}
    E.Signal(I)
Send12(E:event(event(event(event(event(event(event(event(event(event(event(event(int)))))))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(event(event(event(event(event(int))))))))))){}
    spawn{Send11(I)}
    E.Signal(I)
Send13(E:event(event(event(event(event(event(event(event(event(event(event(event(event(int))))))))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(event(event(event(event(event(event(int)))))))))))){}
    spawn{Send12(I)}
    E.Signal(I)
Send14(E:event(event(event(event(event(event(event(event(event(event(event(event(event(event(int)))))))))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(event(event(event(event(event(event(event(int))))))))))))){}
    spawn{Send13(I)}
    E.Signal(I)
Send15(E:event(event(event(event(event(event(event(event(event(event(event(event(event(event(event(int))))))))))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(event(event(event(event(event(event(event(event(int)))))))))))))){}
    spawn{Send14(I)}
    E.Signal(I)
Send16(E:event(event(event(event(event(event(event(event(event(event(event(event(event(event(event(event(int)))))))))))))))))<suspends>:void =
    Sleep(0.0)
    I := event(event(event(event(event(event(event(event(event(event(event(event(event(event(event(int))))))))))))))){}
    spawn{Send15(I)}
    E.Signal(I)
F0()<suspends>:int =
    Sleep(0.0)
    8
F1()<suspends>:task(int) =
    Sleep(0.0)
    spawn{F0()}
F2()<suspends>:task(task(int)) =
    Sleep(0.0)
    spawn{F1()}
F3()<suspends>:task(task(task(int))) =
    Sleep(0.0)
    spawn{F2()}
F4()<suspends>:task(task(task(task(int)))) =
    Sleep(0.0)
    spawn{F3()}
F5()<suspends>:task(task(task(task(task(int))))) =
    Sleep(0.0)
    spawn{F4()}
F6()<suspends>:task(task(task(task(task(task(int)))))) =
    Sleep(0.0)
    spawn{F5()}
F7()<suspends>:task(task(task(task(task(task(task(int))))))) =
    Sleep(0.0)
    spawn{F6()}
F8()<suspends>:task(task(task(task(task(task(task(task(int)))))))) =
    Sleep(0.0)
    spawn{F7()}
F9()<suspends>:task(task(task(task(task(task(task(task(task(int))))))))) =
    Sleep(0.0)
    spawn{F8()}
F10()<suspends>:task(task(task(task(task(task(task(task(task(task(int)))))))))) =
    Sleep(0.0)
    spawn{F9()}
F11()<suspends>:task(task(task(task(task(task(task(task(task(task(task(int))))))))))) =
    Sleep(0.0)
    spawn{F10()}
F12()<suspends>:task(task(task(task(task(task(task(task(task(task(task(task(int)))))))))))) =
    Sleep(0.0)
    spawn{F11()}
F13()<suspends>:task(task(task(task(task(task(task(task(task(task(task(task(task(int))))))))))))) =
    Sleep(0.0)
    spawn{F12()}
F14()<suspends>:task(task(task(task(task(task(task(task(task(task(task(task(task(task(int)))))))))))))) =
    Sleep(0.0)
    spawn{F13()}
F15()<suspends>:task(task(task(task(task(task(task(task(task(task(task(task(task(task(task(int))))))))))))))) =
    Sleep(0.0)
    spawn{F14()}
# (an event of an event of an event(): the last call is the event's Signal)
SendTwo(E:event(event(event())))<suspends>:void =
    Sleep(0.0)
    M := event(event()){}
    spawn{SendOne(M)}
    E.Signal(M)
SendOne(M:event(event()))<suspends>:void =
    Sleep(0.0)
    I := event(){}
    I.Subscribe(On)
    M.Signal(I)
Main()<suspends>:void =
    Effects()
    Hinted()
    E := event(event(event(event(event(event(event(event(event(event(event(event(event(event(event(event(int)))))))))))))))){}
    spawn{Send16(E)}
    X := E.Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await()
    Print("events gave {X}")
    T := spawn{F15()}
    Y := T.Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await().Await()
    Print("tasks gave {Y}")
    G := event(event(event())){}
    spawn{SendTwo(G)}
    G.Await().Await().Signal()
    Print("done")
