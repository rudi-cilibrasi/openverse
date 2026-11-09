# methods as values by variance (#231): a method of a class without type
# parameters at a closed function type it fits, holding the receiver
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
describer := class:
    Describe(A:animal):string = "an {A.Name()}"
    Count():int = 3
OnDog(F:type{_(:dog):string}, D:dog):string = F(D)
Ratio(F:type{_():rational}):int = Floor(F())
Main():void =
    Obj := describer{}
    F:type{_(:dog):string} = Obj.Describe
    Print(F(dog{}))
    Print(OnDog(Obj.Describe, dog{}))
    Print("{Ratio(Obj.Count)}")
