# function values by variance and generic functions as values (#214): a
# function of an animal where one of a dog is expected, an int result where
# a rational one is, a generic function at the closed types expected
animal := class:
    Name:string
dog := class(animal):
    Barks:int = 1
Describe(A:animal)<transacts>:string = "an animal named {A.Name}"
Count()<transacts>:int = 3
Id(X:t where t:type)<transacts>:t = X
Pair(X:t, Y:t where t:type)<transacts>:[]t = array{X, Y}
OnDog(F:type{_(:dog)<transacts>:string}, D:dog)<transacts>:string = F(D)
Ratio(F:type{_()<transacts>:rational})<transacts>:int = Floor(F())
UseId(F:type{_(:int)<transacts>:int})<transacts>:int = F(5)
UseIdS(F:type{_(:string)<transacts>:string})<transacts>:string = F("s")
Main():void =
    D := dog{Name := "rex"}
    Print(OnDog(Describe, D))
    Print("{Ratio(Count)}")
    Print("{UseId(Id)} {UseIdS(Id)}")
    G:type{_(:tuple(int, int))<transacts>:[]int} = Pair
    for (X : G(1, 2)) { Print("{X}") }
    H:type{_(:dog)<transacts>:string} = Describe
    Print(H(D))
