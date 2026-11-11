sink(t:type) := interface:
    Get(Z:t,?Extra:t)<suspends>:t
k(u:type) := class(sink([]u)):
    X:u
    Get<override>(Z:[]u,?Extra:[]u=block{Print("default");Concatenate()})<suspends>:[]u=
        Sleep(0.01)
        Z+Extra+array{X}
Start(P:sink(t),Z:t where t:type):task(t)=spawn{P.Get(Z)}
Main()<suspends>:void=
    T:=Start(k(int){X:=7},array{3})
    Print("started")
    A:=T.Await()
    Print("length {A.Length}")
