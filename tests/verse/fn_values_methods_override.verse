# methods as values (#219): an override's narrower result type is the
# value's, at the receiver's static class; a non-generic class's override
# of a generic interface's method is a value; a method a subclass
# overloads is a value where one overload is visible
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
    Bark():string = "woof"
maker := class:
    Make():animal = animal{}
dogmaker := class(maker):
    Make<override>():dog = dog{}
getter(t:type) := interface:
    All():[]t
ints := class(getter(int)):
    All<override>():[]int = array{1, 2}
base := class:
    M(X:int):int = X + 1
child := class(base):
    M(X:string):string = X
Apply(F:int->int):int = F(1)
Main():void =
    D := dogmaker{}
    F := D.Make
    Print(F().Bark())
    G:type{_():dog} = D.Make
    Print(G().Name())
    M:maker = D
    H := M.Make
    Print(H().Name())
    A := ints{}.All
    Print("{A().Length}")
    Print("{Apply(base{}.M)}")
