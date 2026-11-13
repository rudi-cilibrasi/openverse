# Type aliases of classes, interfaces, structs, enums and refinement types
# stand for them as types, and where a construction, a cast, a parent, a
# qualifier or an enum's value names them (Book of Verse tests, TypeAlias)
named := shape                 # (an alias may name a class defined after it)
shape := class:
    Size:int = 26
    Area():int = Size
square := class(named):
    Bigger():int = (named:)Area() + 1
greeter := interface:
    Greet():string
hello := greeter
english := class(hello):
    Greet<override>():string = "hello"
point := struct:
    X:int
    Y:int
pt := point
colour := enum{Red, Green}
hue := colour
age := type{_X:int where 0 <= _X, _X <= 120}
years := age
box(t:type) := class:
    V:t
int_box := box(int)
box_of(t:type) := box(t)
pair_box(t:type) := box(tuple(t, t))

Shade(C:colour):hue = C
Speak(G:hello):string = G.Greet()
Total(P:pt):int = P.X + P.Y

Main():void =
    Print("{named{}.Area()} {square{}.Bigger()}")
    S:named = square{}
    if (Q := square[S]) then Print("a square of {Q.Bigger()}")
    Print(Speak(english{}))
    Print("{Total(pt{X := 3, Y := 4})}")
    if (Shade(hue.Green) = colour.Green) then Print("green")
    Y:years = 30
    if (Z := years[Y + 100]) then Print("{Z}") else Print("not an age")
    B := int_box{V := 5}
    D:box_of(string) = box_of(string){V := "s"}
    E:pair_box(int) = box(tuple(int, int)){V := (1, 2)}
    Print("{B.V} {D.V} {E.V(1)}")
