# Bound methods with named parameters as values (#503): the receiver is
# evaluated once, when the value is made; each call evaluates the omitted
# defaults then, reading the receiver's current fields, and dispatches as a
# call does, so an override's own default is the one that runs (Book of
# Verse ch. 6: defaults read the instance's overridden members). An
# override with a default of its own is a value of a type that omits it.
game := class:
    var DefaultSpeed:float = 1.0
    CurrentSpeed(?Speed:float = DefaultSpeed)<transacts>:float = Speed
base_game := class:
    DefaultSpeed:float = 1.0
    Speed(?Factor:float = DefaultSpeed)<computes>:float = Factor
fast_game := class(base_game):
    DefaultSpeed<override>:float = 2.0
slow_game := class(base_game):
    Speed<override>(?Factor:float = 0.25)<computes>:float = Factor * 2.0
shape := interface:
    Area(?Scale:int = 1):int
square := class(shape):
    Side:int
    Area<override>(?Scale:int = 2):int = Side * Side * Scale
rect := class(shape):
    W:int
    H:int
    Area<override>(?Scale:int = 3):int = W * H * Scale
box(t:type) := class:
    V:t
    Get(?Or:t = V):t = Or
strict := class:
    Pick(?X:int):int = X
lenient := class(strict):
    Pick<override>(?X:int = 5):int = X + 1
MakeGame():game =
    Print("receiver")
    game{}
Main():void =
    F:type{_():float} = MakeGame().CurrentSpeed
    Print("bound")
    Print("{F()} {F()}")
    G := game{}
    H:type{_():float} = G.CurrentSpeed
    K:type{_(?Speed:float):float} = G.CurrentSpeed
    set G.DefaultSpeed = 3.0
    Print("{H()} {K(?Speed := 0.5)}")
    Games:[]base_game = array{base_game{}, fast_game{}, slow_game{}}
    for (B : Games):
        S:type{_():float} = B.Speed
        Print("{S()}")
    Shapes:[]shape = array{square{Side := 2}, rect{W := 2, H := 3}}
    for (Sh : Shapes):
        A:type{_():int} = Sh.Area
        A10:type{_(?Scale:int):int} = Sh.Area
        Print("{A()} {A10(?Scale := 10)}")
    Bx := box(string){V := "v"}
    Get:type{_():string} = Bx.Get
    GetOr:type{_(?Or:string):string} = Bx.Get
    Print("{Get()} {GetOr(?Or := "w")}")
    Le := lenient{}
    P:type{_():int} = Le.Pick
    St:strict = Le
    Q:type{_(?X:int):int} = St.Pick
    Print("{P()} {Q(?X := 1)}")
