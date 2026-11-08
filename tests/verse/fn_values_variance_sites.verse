# function values by variance and generic functions as values wherever the
# elaborator expects a closed function type (#214): a generic method's
# parameter at the type it is called at (Subscribe), a result, a var set,
# a map literal, a class below a generic parent, a named argument; two
# values of one shape at different types
animal := class:
    Name:string
dog := class(animal):
    B:int = 1
pet(t:type) := class(animal):
    V:t
cat := class(pet(int)):
    C:int = 2
Hear(A:animal):void = Print("heard {A.Name}")
Desc(A:animal):string = "an animal named {A.Name}"
Id(X:t where t:type):t = X
Pick(B:logic):type{_(:dog):string} = Desc
UseD(F:type{_(:dog):string}, D:dog):string = F(D)
UseC(F:type{_(:cat):string}, C:cat):string = F(C)
Opt(D:dog, ?F:type{_(:dog):string} = Desc):string = F(D)
Main():void =
    K := Desc
    Print(K(dog{Name := "k"}))
    E := subscribable_event(dog){}
    S := E.Subscribe(Hear)
    E.Signal(dog{Name := "d"})
    Print(Pick(true)(dog{Name := "p"}))
    var V:type{_(:dog):string} = Desc
    set V = Desc
    Print(V(dog{Name := "v"}))
    M:[int]type{_(:dog):string} = map{1 => Desc}
    if (F := M[1]) then Print(F(dog{Name := "m"}))
    Print(UseC(Desc, cat{Name := "c", V := 1}))
    Print(Opt(dog{Name := "o"}, ?F := Desc))
    G:int->int = Id
    Print("{G(4)}")
