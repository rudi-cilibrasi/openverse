# function values by variance and generic functions as values (#214): a
# function of an animal where one of a dog is expected, an int result where
# a rational one is, a generic function at the closed types expected
animal := class:
    Name:string
dog := class(animal):
    Barks:int = 1
Describe(A:animal):string = "an animal named {A.Name}"
Count():int = 3
Id(X:t where t:type):t = X
Pair(X:t, Y:t where t:type):[]t = array{X, Y}
OnDog(F:type{_(:dog):string}, D:dog):string = F(D)
Ratio(F:type{_():rational}):int = Floor(F())
UseId(F:int->int):int = F(5)
UseIdS(F:string->string):string = F("s")
Main():void =
    D := dog{Name := "rex"}
    Print(OnDog(Describe, D))
    Print("{Ratio(Count)}")
    Print("{UseId(Id)} {UseIdS(Id)}")
    G:tuple(int, int)->[]int = Pair
    for (X : G(1, 2)) { Print("{X}") }
    H:type{_(:dog):string} = Describe
    Print(H(D))
