# Classes, phase 2 (#18; Book of Verse ch. 10): single inheritance, abstract
# classes, interfaces, overriding, (super:), virtual dispatch, casts.

shape := class<abstract>:
    Name:string = "shape"
    Area():int
    Describe():string = "{Name} of area {Area()}"

square := class(shape):
    Side:int
    Area<override>():int = Side * Side

labelled := interface:
    Label():string
    # a default method
    Shout():string = "{Label()}!"

circle := class(shape, labelled):
    Name<override>:string = "circle"
    R:int
    Area<override>():int = 3 * R * R
    Label<override>():string = "a circle of radius {R}"
    Describe<override>():string = "round: {(super:)Describe()}"

# two levels, and an override of an override
cube := class(square):
    Name<override>:string = "cube"
    Area<override>():int = 6 * (super:)Area()

# an interface implemented by an unrelated class
tag := class(labelled):
    Text:string
    Label<override>():string = Text

# a <decides> virtual method
animal := class<abstract>:
    Legs():int
    Walks()<decides>:void = Legs() > 0

fish := class(animal):
    Legs<override>():int = 0

dog := class(animal):
    Legs<override>():int = 4
    Fetch():string = "fetching"

# the most specific implementation wins, whatever the order of the parents
greeter := interface:
    Greet():string = "hello"
polite := interface(greeter):
    Greet<override>():string = "good day"
host := class(greeter, polite):
    Name:string = "host"

# a class parent and an interface, both above two classes
named := interface:
    Title():string
pet := class:
    Age:int = 1
cat := class(pet, named):
    Title<override>():string = "cat"
bird := class(pet, named):
    Title<override>():string = "bird"

Identity(X:t where t:type):t = X

# classes and interfaces in generic code, and as parameters
Labels(Items:[]labelled):[]string = for (I : Items) { I.Label() }

Largest(Shapes:[]shape):string =
    var Best:string = "none"
    var Top:int = -1
    for (S : Shapes, S.Area() > Top):
        set Top = S.Area()
        set Best = S.Name
    Best

Count(Items:[]t where t:type):int = Items.Length

Main():void =
    Shapes:[]shape = array{square{Side := 2}, circle{R := 1}, cube{Side := 1}}
    for (S : Shapes) { Print(S.Describe()) }
    Print("largest: {Largest(Shapes)}")
    # casts: T[X] fails unless X's class is below T
    for (S : Shapes, C := circle[S]) { Print(C.Label()) }
    for (S : Shapes, Sq := square[S]) { Print("a square of side {Sq.Side}") }
    Ls:[]labelled = array{circle{R := 2}, tag{Text := "hello"}}
    for (L : Labels(Ls)) { Print(L) }
    for (L : Ls) { Print(L.Shout()) }
    if (T := tag[Ls[1]]) then Print("tag says {T.Text}")
    if (not circle[Ls[1]]) then Print("a tag is not a circle")
    # an infallible upcast
    Sh := shape(cube{Side := 3})
    Print("{Sh.Name}: {Sh.Area()}")
    # an option of a subclass where an option of the base is expected
    O:?shape = option{square{Side := 5}}
    if (Inner := O?) then Print("option holds area {Inner.Area()}")
    # branches join at their common superclass
    Pick := if (Sh.Area() > 100) then square{Side := 1} else circle{R := 3}
    Print("picked {Pick.Name}")
    Animals:[]animal = array{fish{}, dog{}}
    for (A : Animals):
        if (A.Walks[]) then Print("walks on {A.Legs()} legs") else Print("swims")
    for (A : Animals, D := dog[A]) { Print(D.Fetch()) }
    Print("{Count(Animals)} animals")
    Print(host{}.Greet())
    G:greeter = host{}
    Print(G.Greet())
    # the expected type of an if: a common interface, not the common class
    N:named = if (Count(Animals) > 1) then cat{} else bird{}
    Print(N.Title())
    # a cast used only as a condition, and a subclass passed to a generic function
    if (dog[Animals[1]]) then Print("the second animal is a dog")
    A2:animal = Identity(dog{})
    Print("{A2.Legs()} legs")
    # a failing cast inside a failure context rolls back
    var Seen:int = 0
    if (set Seen += 1, D := dog[Animals[0]]) then Print("unreachable")
    Print("Seen = {Seen}")
