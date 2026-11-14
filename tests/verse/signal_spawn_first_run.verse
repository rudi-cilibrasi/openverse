# A request and its answer inside one spawn's first run (the Book's ch. 14,
# "a spawned body runs up to its first suspension point immediately", and
# the request/response example): the reply task parks first, the request's
# Signal runs the service, whose Signal runs the reply task to its end, so
# awaiting it does not suspend; Main reads the answer right after spawn
cell := class:
    var V:int = 0
Service(Req:event(int), Resp:event(int))<suspends>:void =
    loop:
        R := Req.Await()
        Resp.Signal(R * 10)
Ask(Req:event(int), Resp:event(int), N:int)<suspends>:int =
    Reply:task(int) = spawn{Resp.Await()}
    Req.Signal(N)
    Reply.Await()
Driver(Req:event(int), Resp:event(int), Out:cell)<suspends>:void =
    set Out.V = Ask(Req, Resp, 4)
    Print("driver has {Out.V}")
    set Out.V += Ask(Req, Resp, 7)
Main():void =
    Req := event(int){}
    Resp := event(int){}
    Out := cell{}
    spawn{Service(Req, Resp)}
    spawn{Driver(Req, Resp, Out)}
    Print("after spawn {Out.V}")
