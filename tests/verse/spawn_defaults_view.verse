first(t:type) := interface { Tag():t }
sink(t:type) := interface { Get(?N:int=0)<suspends>:int }
both(a:type,b:type) := class(first(a),sink(b)):
    V:a
    Seed:int=4
    Tag<override>():a=V
    Get<override>(?N:int=block{E:[]b=Concatenate();Seed+E.Length})<suspends>:int=
        Sleep(0.01)
        N
Start(P:sink(t) where t:type):task(int)=spawn{P.Get()}
Main()<suspends>:void=
    T:=Start(both(int,string){V:=7})
    Print("started")
    Print("result {T.Await()}")
