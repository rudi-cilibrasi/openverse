# Values of functions with named parameters escape (#503): returned from a
# function, kept in a var, an option, a map, an array and a field, and
# called after their creator returns. An unannotated value keeps its own
# named type, and a value converts to the function types above its own
# (names it may omit left out), as the Book's subtyping has it.
Greet(Name:string, ?Greeting:string = "Hello"):string = "{Greeting}, {Name}!"
Shout(Name:string, ?Volume:int = 3):string = "HEY {Name} {Volume}"
Pick(Polite:logic):type{_(:string):string} = if (Polite?) then Greet else Shout
Each(Xs:[]string, F:type{_(:string):string}):void =
    for (X : Xs) { Print(F(X)) }
F6(?A:int = 6):int = A
holder := class:
    Fn:type{_(?A:int = 0):int}
Main():void =
    var F:type{_(:string):string} = Pick(true)
    Print(F("Ann"))
    set F = Pick(false)
    Print(F("Bob"))
    O:?type{_(:string, ?Greeting:string):string} = option{Greet}
    if (G := O?) then Print(G("Cy", ?Greeting := "Hi"))
    M:[int]type{_(:string):string} = map{1 => Greet, 2 => Shout}
    if (H := M[2]) then Print(H("Di"))
    Fs:[]type{_(:string):string} = array{Greet, Shout}
    Each(array{"Ed"}, Greet)
    for (Fn : Fs) { Print(Fn("Flo")) }
    Own := Greet
    Print(Own("Gus", ?Greeting := "Hey"))
    Each(array{"Hal"}, Own)
    Hd := holder{Fn := F6}
    Up:type{_():int} = Hd.Fn
    Print("{Hd.Fn()} {Hd.Fn(?A := 1)} {Up()}")
