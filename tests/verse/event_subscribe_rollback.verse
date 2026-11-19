# (#724) An event's Subscribe and a subscription's Cancel in a failure
# context that fails are undone (the Book, ch. 14, "Transactional
# Behavior"; Epic's API gives both <transacts>: followup-event/
# subscribe-rollback and cancel-rollback ask the Verse VM), also inside a
# <transacts><decides> function that fails; both are admitted in a
# <transacts> function and a failure context, not only in Main
counter := class:
    var Seen:int = 0
    Receive(N:int):void =
        set Seen += N
TryAttach(E:event(int), F:type{_(:int):void})<transacts><decides>:cancelable =
    S := E.Subscribe(F)
    false?
    S
Main():void =
    E := event(int){}
    C := counter{}
    if (S := E.Subscribe(C.Receive), false?) then Print("no") else Print("subscribe undone")
    E.Signal(1)
    Print("seen {C.Seen}")
    if (T := TryAttach[E, C.Receive]) then Print("no") else Print("attach undone")
    E.Signal(2)
    Print("seen {C.Seen}")
    K := E.Subscribe(C.Receive)
    if (K.Cancel(), false?) then Print("no") else Print("cancel undone")
    E.Signal(3)
    Print("seen {C.Seen}")
    if (K.Cancel(), true?) then Print("cancelled")
    E.Signal(4)
    Print("seen {C.Seen}")
