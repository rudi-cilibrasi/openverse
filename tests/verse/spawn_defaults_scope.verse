root(t:type) := interface:
    Read()<computes>:int=1
    Go(?N:int=0)<suspends>:int=N
wrap(u:type) := interface(root([]u)):
    Go<override>(?N:int=block{E:[]u=Concatenate();(super:)Read()+E.Length})<suspends>:int=block{Sleep(0.01);N}
c(t:type) := class(wrap(t)) {}
Start(P:root(a) where a:type):task(int)=spawn{P.Go()}
Main()<suspends>:void=
    T:=Start(c(int){})
    Print("result {T.Await()}")
