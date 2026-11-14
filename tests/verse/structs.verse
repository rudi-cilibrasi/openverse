# Structs and enums (Book of Verse ch. 9).
vector2 := struct:
    X:int = 0
    Y:int = 0

player := struct:
    Name:string
    Pos:vector2 = vector2{}
    Score:int = 0

suit := enum:
    Hearts
    Spades
    Clubs

Add(A:vector2, B:vector2):vector2 = vector2{X := A.X + B.X, Y := A.Y + B.Y}

SuitName(S:suit):string =
    case (S):
        suit.Hearts => "hearts"
        suit.Spades => "spades"
        suit.Clubs => "clubs"

IsRed(S:suit)<decides>:void =
    S = suit.Hearts

Main():void =
    V := Add(vector2{X := 1, Y := 2}, vector2{Y := 10})
    Print("({V.X}, {V.Y})")
    var P:player = player{Name := "Ana"}
    set P.Score += 5
    set P.Score += 3
    Print("{P.Name} has {P.Score} points at ({P.Pos.X}, {P.Pos.Y})")
    if (P = player{Name := "Ana", Score := 8}) { Print("structs compare by value") }
    for (S : array{suit.Hearts, suit.Spades, suit.Clubs}):
        if (IsRed[S]) then Print("{SuitName(S)} are red") else Print("{SuitName(S)} are black")
