# Type aliases (Book of Verse ch. 10, "Aliases"; ch. 11, "Type Aliases"): a
# name for a type, which stands for it wherever it is used
player_id := int
game_id := player_id
maybe := ?int
maybe2 := ?maybe
ints := []int
scores := [string]int
unary := int -> int
thunk := type{_():int}
point := tuple(float, float)
nothing := tuple()
flag := logic
pair_of(t:type) := tuple(t, t)
string_map(t:type) := [string]t
optional_array(t:type) := []?t
transformer(a:type, b:type) := a -> b
twice(t:type) := pair_of(pair_of(t))

ProcessPlayer(ID:player_id):game_id = ID + 1
Unwrap(O:maybe2)<decides>:int = O??
Sum(X:ints):int =
    var R:int = 0
    for (Y : X) { set R += Y }
    R
Apply(G:unary, X:int):int = G(X)
Call(G:thunk):int = G()
Inc(X:int):int = X + 1
Seven():int = 7
Swap(P:pair_of(int)):pair_of(int) = (P(1), P(0))
Valid(Items:optional_array(int)):[]int = for (Item : Items; Value := Item?) { Value }
Show(T:transformer(int, string), V:int):string = T(V)
Str(X:int):string = "<{X}>"
Corner(Q:twice(int)):int = Q(1)(0)
Both(F:flag):string = if (F?) then "yes" else "no"

Main():void =
    G:game_id = 41
    Print("{ProcessPlayer(G)} {ProcessPlayer(1)}")
    if (V := Unwrap[option{option{2}}]) then Print("{V}")
    if (not Unwrap[option{false}]) then Print("empty inside")
    Print("{Sum(array{1, 2, 3})}")
    Scores:string_map(int) = map{"a" => 1, "b" => 2}
    W:scores = Scores
    if (S := W["b"]) then Print("{S}")
    Print("{Apply(Inc, 10)} {Call(Seven)}")
    C:point = (1.5, 2.5)
    Print("{C(1)}")
    P := Swap((3, 4))
    Print("{P(0)} {P(1)}")
    for (I : Valid(array{option{5}, false, option{6}})) { Print("{I}") }
    Print(Show(Str, 12))
    Print("{Corner(((1, 2), (3, 4)))}")
    N:nothing = ()
    Print(Both(true))
