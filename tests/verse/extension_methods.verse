# Extension methods (Book of Verse ch. 6, "Extension Methods"): (R:t).M(…)
# is the function $ext:M whose first parameter is the receiver, called X.M(…)
# on a receiver of any type, overloaded by the receiver's type

(Value:int).Double()<computes>:int = Value * 2
(N:int).IsEven()<decides><computes>:void = Mod[N, 2] = 0
(S:string).FirstChar()<decides><computes>:char = S[0]

# overloads, told apart by the receiver's type
(N:int).Format():string = "int:{N}"
(B:logic).Format():string = if (B?) then "logic:true" else "logic:false"
(F:float).Format():string = "float:{F}"
(C:char).Format():string = "char:{C}"
(P:tuple(int, int)).Format():string = "pair:{P(0)},{P(1)}"
(A:[]int).Size():string = "array of {A.Length}"
(M:[int]string).Entries():string = "map of {M.Length}"
(O:?int).Show():string = if (V := O?) then "some {V}" else "none"

# named parameters and defaults
(Text:string).Wrap(Open:string, ?Close:string = ">")<computes>:string = "{Open}{Text}{Close}"

# a tuple receiver, and the unit
(Point:tuple(int, int)).Dot(Other:tuple(int, int))<computes>:int = Point(0) * Other(0) + Point(1) * Other(1)
(:tuple()).Magic():int = 42

# arrays and maps
(Vals:[]int).Sum()<transacts>:int =
    var Total:int = 0
    for (N : Vals):
        set Total += N
    Total
(M:[int]string).Keys()<computes>:[]int = for (Key -> X : M) { Key }

# classes, structs, enums and interfaces
player := class:
    Name:string
    var Score:int
(P:player).AddScore(Points:int)<transacts>:void = set P.Score += Points

point := struct:
    X:int
    Y:int
(P:point).Translate(DX:int, DY:int):point = point{X := P.X + DX, Y := P.Y + DY}

dir := enum{North, South}
(D:dir).Opposite():dir = if (D = dir.North) then dir.South else dir.North

named := interface:
    Label():string
dog := class(named):
    Label<override>():string = "dog"
(N:named).Shout():string = "{N.Label()}!"

# a field of one class and an extension method of another, of one name
with_q := class{Q:int = 10}
without_q := class{}
(:without_q).Q():int = 11

# generic receivers: a where in the receiver's parentheses, and in the
# parameters'
(X:t where t:type).Twice():tuple(t, t) = (X, X)
(Xs:[]t where t:subtype(comparable)).Count(Y:t):int =
    var N:int = 0
    for (X : Xs, X = Y):
        set N += 1
    N
(Xs:[]t where t:type).Zip(Ys:[]u where u:type):[]tuple(t, u) =
    for (I -> X : Xs, Y := Ys[I]) { (X, Y) }

# recursion, and one extension method calling another
(N:int).Fact():int = if (N <= 1) then 1 else N * (N - 1).Fact()
(N:int).Quadruple():int = N.Double().Double()

# the receiver is evaluated once, before the arguments
Note(S:string, V:int):int =
    Print(S)
    V
(A:int).Plus(B:int):int = A + B

Main():void =
    X := 5
    Print("{X.Double()} {7.Double()} {(2).Double()}")
    if (42.IsEven[]) then Print("42 is even")
    if (not 7.IsEven[]) then Print("7 is odd")
    if ("Hello".FirstChar[] = 'H') then Print("starts with H")
    if (not "".FirstChar[]) then Print("no first char")
    Print(42.Format())
    Print(true.Format())
    Print(1.5.Format())
    Print('c'.Format())
    Print((1, 2).Format())
    Print(array{1, 2, 3}.Size())
    Print(map{1 => "a"}.Entries())
    Some:?int = option{4}
    None:?int = false
    Print("{Some.Show()} {None.Show()}")
    Print("{"a".Wrap("<")} {"a".Wrap("[", ?Close := "]")}")
    Print("{(1, 2).Dot((3, 4))} {().Magic()}")
    Print("{array{1, 2, 3, 4, 5}.Sum()}")
    for (K : map{3 => "c", 1 => "a"}.Keys()) { Print("key {K}") }
    P := player{Name := "Alice", Score := 100}
    P.AddScore(50)
    Print("{P.Name} {P.Score}")
    Origin := point{X := 0, Y := 0}
    Delta := (5, 10)
    Moved := Origin.Translate(Delta)
    Print("{Moved.X} {Moved.Y}")
    if (dir.North.Opposite() = dir.South) then Print("opposite")
    Print(dog{}.Shout())
    Print("{with_q{}.Q} {without_q{}.Q()}")
    T := "x".Twice()
    Print("{T(0)}{T(1)} {array{1, 2, 1, 1}.Count(1)}")
    for (Pair : array{1, 2, 3}.Zip(array{"a", "b"})) { Print("{Pair(0)}{Pair(1)}") }
    Print("{5.Fact()} {3.Quadruple()} {5.Double().Double()}")
    var V:int = 3
    Print("{V.Double()}")
    Print("{Note("receiver", 1).Plus(Note("argument", 2))}")
