# Function values of functions with named parameters by variance (#214,
# #503): a named parameter's type above the type's and a result below, as
# a call converts them, for functions and bound methods; and a parameter of
# a function type above the expected one's (a function type with an
# optional parameter is below the same type requiring it).
Scale(X:rational, ?By:rational = 2):rational = X * By
animal := class:
    Name:string = "animal"
dog := class(animal):
    Name<override>:string = "dog"
Describe(A:animal, ?Prefix:string = "a "):string = Prefix + A.Name
speaker := class:
    (speaker:)Describe(A:animal, ?Prefix:string = "the "):string = Prefix + A.Name
Use(F:type{_(?A:int):int}):int = F(?A := 1)
Opt(?A:int = 5):int = A
Main():void =
    F:type{_(:int, ?By:int):rational} = Scale
    G:type{_(:int):rational} = Scale
    Print("{Floor(F(3, ?By := 3))} {Floor(G(3))}")
    H:type{_(:dog):string} = Describe
    K:type{_(:dog, ?Prefix:string):string} = Describe
    Print("{H(dog{})} {K(dog{}, ?Prefix := "my ")}")
    S := speaker{}
    SH:type{_(:dog):string} = S.Describe
    Print(SH(dog{}))
    U:type{_(:type{_(?A:int = 0):int}):int} = Use
    Print("{U(Opt)}")
