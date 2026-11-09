# subscribable_event() (#220): an event without a value, whose subscribed
# functions take none: a field with its default, a method subscribed that
# cancels itself, a task awaiting it (woken before the functions are called,
# going on after Signal), a Subscribe undone by a failing condition
button := class:
    Pressed:subscribable_event() = subscribable_event(){}
    Press():void = Pressed.Signal()
door := class:
    var Opens:int = 0
    B:button
    var Sub:?cancelable = false
    Attach():void =
        set Sub = option{B.Pressed.Subscribe(OnPress)}
    OnPress():void =
        set Opens += 1
        if (Opens > 1, S := Sub?) then S.Cancel()
Ping():void = Print("ping")
Waiter(E:subscribable_event())<suspends>:void =
    E.Await()
    Print("woken")
Main()<suspends>:void =
    B1 := button{}
    D := door{B := B1}
    D.Attach()
    B1.Press()
    B1.Press()
    B1.Press()
    Print("opens {D.Opens}")
    E := subscribable_event(){}
    C := E.Subscribe(Ping)
    T := spawn{Waiter(E)}
    E.Signal()
    T.Await()
    C.Cancel()
    E.Signal()
    if (X := E.Subscribe(Ping), false?):
        Print("never")
    E.Signal()
    Print("done")
