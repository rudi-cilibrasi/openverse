leading(a:type) := interface { Tag():a }
sink(b:type) := interface { Get(?Extra:b)<suspends>:b }
both(a:type,b:subtype(comparable)) := class(leading(a),sink(b)):
    V:a
    SeedB:b
    Tag<override>():a=V
    Get<override>(?Extra:b=block{if(SeedB=SeedB)then SeedB else SeedB})<suspends>:b=block{Sleep(0.01);Extra}
Start(P:sink(t) where t:type):task(t)=spawn{P.Get()}
Main()<suspends>:void=
    T:=Start(both(int,string){V:=7,SeedB:="payload"})
    Print("started")
    Print("result {T.Await()}")
