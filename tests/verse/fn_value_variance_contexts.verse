# (#724) a function value converted by class variance (contravariant
# parameters, a covariant result: a class or an interface below or above), as
# Epic's Verse compiler converts any function value whose conversion needs no
# wrapper (UEFN 43.12, followup-coerce's value-class-variance,
# followup-coerce2's value-class-result), in each place a value is converted:
# a local, a parameter, a var's set, a field given and set, a call's result,
# a function's result, the branches of an if (at an expected type, and at
# their join: each parameter the lower, the result the join), and arrays,
# options, tuples and maps of such values.
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
pet := interface:
    Purr():string
cat := class(animal, pet):
    Name<override>():string = "cat"
    Purr<override>():string = "purr"

Describe(A:animal):string = "an {A.Name()}"
MakeDog():dog = dog{}
MakeCat():cat = cat{}
Stroke(P:pet):string = P.Purr()
OnlyDog(X:dog):string = "only {X.Name()}"

RunDog(F(:dog):string):string = F(dog{})
RunCat(F(:cat):string):string = F(cat{})
RunAnimal(F():animal):string = F().Name()
RunPet(F():pet):string = F().Purr()

holder := class:
    Take:type{_(:dog):string}
    var Make:type{_():animal}

DogMaker():type{_():dog} = MakeDog
Widen(F:type{_():dog}):type{_():animal} = F
Pick(Flag:logic, D:type{_():dog}, C:type{_():cat}):type{_():animal} =
    if (Flag?) then D else C

Main():void =
    D:type{_(:animal):string} = Describe
    M:type{_():dog} = MakeDog
    C:type{_():cat} = MakeCat
    S:type{_(:pet):string} = Stroke
    # a local passed as a parameter, a parameter's type both ways
    Print(RunDog(D))
    Print(RunAnimal(M))
    # an interface, a parameter and a result
    Print(RunCat(S))
    Print(RunPet(C))
    # a local's value, and a var set
    L:type{_(:dog):string} = D
    Print(L(dog{}))
    var V:type{_():animal} = M
    Print(V().Name())
    set V = C
    Print(V().Name())
    # a field given at construction, and one set
    H:holder = holder{Take := D, Make := M}
    Print(H.Take(dog{}))
    Print(H.Make().Name())
    set H.Make = C
    Print(H.Make().Name())
    # a call's result, a function's result, an if's branches
    Print(RunAnimal(DogMaker()))
    Print(Widen(M)().Name())
    Print("{Pick(true, M, C)().Name()} {Pick(false, M, C)().Name()}")
    J := if (false?) then M else C
    Print(J().Name())
    Od:type{_(:dog):string} = OnlyDog
    Jd := if (true?) then D else Od
    Print(Jd(dog{}))
    # an array, an option, a tuple and a map of such values
    Fs:[]type{_():animal} = array{M, C}
    for (F : Fs) { Print(F().Name()) }
    Ds:[]type{_(:animal):string} = array{D}
    Es:[]type{_(:dog):string} = Ds
    for (F : Es) { Print(F(dog{})) }
    O:?type{_():dog} = option{M}
    P:?type{_():animal} = O
    if (F := P?) { Print(F().Name()) }
    T:tuple(type{_():dog}, int) = (M, 3)
    U:tuple(type{_():animal}, int) = T
    Print("{U(0)().Name()} {U(1)}")
    Mp:[int]type{_():dog} = map{1 => M, 2 => M}
    Mq:[int]type{_():animal} = Mp
    for (K -> F : Mq) { Print("{K} {F().Name()}") }
