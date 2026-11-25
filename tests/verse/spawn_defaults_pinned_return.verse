# (#724: a class implements an interface's abstract method itself, or a class
# below the interface does: a method of its name from a class that is not below
# the interface is that class's own; UEFN 43.12 error 3591,
# followup-book2/final-method-interface)
animal(t:type) := class { Value:t }
dog(t:type) := class(animal(t)) { Woof():int=1 }
carrier(t:type) := class:
    Value:t
    Seed:int=4
    Get(?N:int=Seed)<suspends>:t=block{Sleep(0.01);Value}
out(v:type) := interface:
    Get(?N:int=0)<suspends>:v
child(u:type) := class(carrier(dog(u)),out(animal(u))):
    Get<override>(?N:int=Seed)<suspends>:dog(u)=block{Sleep(0.01);Value}
Start(P:out(t) where t:type):task(t)=spawn{P.Get()}
Main()<suspends>:void=
    T:=Start(child(string){Value:=dog(string){Value:="payload"}})
    Print("started")
    A:=T.Await()
    Print("animal {A.Value}")
