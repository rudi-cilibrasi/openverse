# (#724) a function value converted by class variance, as Epic's Verse
# compiler converts any function value whose conversion needs no wrapper
# (UEFN 43.12, followup-coerce's value-class-variance, followup-coerce2's
# value-class-result), at every shape: a parameter that is itself a function
# type (the direction flips) and such a result, named parameters (one a
# caller may omit, whose default is the function's own), <decides>, a
# parametric class's instance in a parameter, void and true results, a
# bound method's value, and a value converted twice. The conversion is not
# seen: the value calls the function with the same effects, its receiver
# is the one it was made with, and ToDiagnostic prints the function.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
puppy := class(dog):
    Name<override>():string = "puppy"
box(t:type) := class:
    Item:t

MakeDog():dog = dog{}
CallMaker(F():animal):string = "maker " + F().Name()
RunDogMaker(G(F():dog):string):string = G(MakeDog)
DogMakerMaker():type{_():dog} = MakeDog
RunMakerMaker(G():type{_():animal}):string = G()().Name()

Tag(A:animal, ?Suffix:string):string = A.Name() + Suffix
RunTag(F(:dog, ?Suffix:string):string):string = F(dog{}, ?Suffix := "!")
Mark(A:animal, ?Suffix:string = "?"):string = A.Name() + Suffix
RunMark(F(:dog, ?Suffix:string = "x"):string):string = F(dog{}) + " " + F(dog{}, ?Suffix := "!")

DogOnly(A:animal)<computes><decides>:string =
    dog[A]
    "a dog"
RunDecides(F(:puppy)<computes><decides>:string):string =
    if (S := F[puppy{}]) then S else "failed"

Unbox(B:box(animal)):string = B.Item.Name()
RunDogBox(F(:box(dog)):string):string = F(box(dog){Item := dog{}})

Bark(A:animal):void = Print("bark {A.Name()}")
RunVoid(F(:dog):void):void = F(dog{})
RunTrue(F(:dog):true):void = F(dog{})

counter := class:
    var Count:int = 0
    Bump(A:animal):int =
        set Count += 1
        Count
RunCount(F(:dog):int):int = F(dog{})

RunPuppy(F(:puppy):string):string = F(puppy{})
Describe(A:animal):string = "an {A.Name()}"

Show(Value:any)<reads>:void = Print(ToDiagnostic(Value).String)

Main():void =
    G:type{_(:type{_():animal}):string} = CallMaker
    Print(RunDogMaker(G))
    H:type{_():type{_():dog}} = DogMakerMaker
    Print(RunMakerMaker(H))
    T:type{_(:animal, ?Suffix:string):string} = Tag
    Print(RunTag(T))
    # a named parameter a caller may omit: the function's own default runs
    Mk:type{_(:animal, ?Suffix:string = "y"):string} = Mark
    Print(RunMark(Mk))
    D:type{_(:animal)<computes><decides>:string} = DogOnly
    Print(RunDecides(D))
    U:type{_(:box(animal)):string} = Unbox
    Print(RunDogBox(U))
    B:type{_(:animal):void} = Bark
    RunVoid(B)
    RunTrue(B)
    C := counter{}
    Bm:type{_(:animal):int} = C.Bump
    First := RunCount(Bm)
    Second := RunCount(Bm)
    Print("{First} {Second} {C.Count}")
    # converted twice: animal to dog, then dog to puppy
    A1:type{_(:animal):string} = Describe
    A2:type{_(:dog):string} = A1
    A3:type{_(:puppy):string} = A2
    Print(RunPuppy(A3))
    # ToDiagnostic sees the function, not the conversion
    Show(A1)
    Show(A3)
    Show(B)
    E:type{_(:dog):void} = B
    Show(E)
