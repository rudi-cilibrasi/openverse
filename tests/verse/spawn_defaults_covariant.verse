animal(t:type) := class:
    Value:t
    N:int=0
dog(t:type) := class(animal(t)):
    Woof():int=1
base(t:type) := class:
    Get(X:t,?N:int=0)<suspends>:animal(t)=animal(t){Value:=X,N:=N}
ib(u:type) := class(base(int)):
    Extra:u
    Seed:int=3
    Get<override>(X:int,?N:int=Seed+X)<suspends>:dog(int)=
        Sleep(0.01)
        dog(int){Value:=X,N:=N}
Start(P:base(t),X:t where t:type):task(animal(t))=spawn{P.Get(X)}
Main()<suspends>:void=
    T:=Start(ib(string){Extra:="x"},4)
    Print("started")
    A:=T.Await()
    Print("animal {A.Value} {A.N}")
