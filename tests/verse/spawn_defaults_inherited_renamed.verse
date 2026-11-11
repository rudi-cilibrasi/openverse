animal(t:type) := class { Value:t }
dog(t:type) := class(animal(t)) { Woof():int=1 }
parent(t:type) := class:
    Seed:int=4
    Get(X:t,?N:int=Seed)<suspends>:dog(t)=block{Sleep(0.01);dog(t){Value:=X}}
sink(v:type) := interface:
    Get(X:v,?N:int=0)<suspends>:animal(v)
child(u:type) := class(parent([]u),sink([]u)) {}
Start(P:sink(t),X:t where t:type):task(animal(t))=spawn{P.Get(X)}
Main()<suspends>:void=
    T:=Start(child(int){},array{7})
    Print("started")
    A:=T.Await()
    Print("length {A.Value.Length}")
