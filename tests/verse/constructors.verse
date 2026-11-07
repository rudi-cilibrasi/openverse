# constructor functions (#11, Book of Verse ch. 10): field initializers in
# order, let:, block:, delegation to the class's or a parent's constructor,
# <decides> and named parameters; the class's own block: runs last

entity := class:
    Name:string
    Level:int = 1
    block:
        Print("entity block")

character := class(entity):
    Health:int

player := class(character):
    var Score:int = 0

MakeEntity<constructor>(N:string, L:int) := entity:
    Name := N
    Level := L

MakeCharacter<constructor>(N:string, L:int) := character:
    Health := L * 100
    MakeEntity<constructor>(N, L)

MakePlayer<constructor>(N:string) := player:
    let:
        L := N.Length
    block:
        Print("making {N}")
    MakeCharacter<constructor>(N, L)

MakeNewPlayer<constructor>(N:string) := player:
    MakePlayer<constructor>(N)

MakeValid<constructor>(N:string, L:int)<decides> := character:
    let:
        Ok := L > 0
    Health := L
    Name := N

MakeNamed<constructor>(?N:string = "anon", ?L:int = 2) := entity:
    Name := N
    Level := L

node := class:
    V:int
    Next:?node = false

MakeList<constructor>(N:int) := node:
    V := N
    Next := if (N > 0) then option{MakeList(N - 1)} else false

MakeT<constructor>(N:string)<transacts> := entity:
    Name := N

Main():void =
    E := MakeEntity("e", 3)
    Print("{E.Name} {E.Level}")
    C := MakeCharacter("c", 4)
    Print("{C.Name} {C.Level} {C.Health}")
    P := MakeNewPlayer("pq")
    set P.Score += 5
    Print("{P.Name} {P.Level} {P.Health} {P.Score}")
    if (V := MakeValid["v", 7]) then Print("valid {V.Health}") else Print("invalid")
    if (V := MakeValid["v", 0]) then Print("valid {V.Health}") else Print("invalid")
    D := MakeNamed(?L := 9)
    Print("{D.Name} {D.Level}")
    var Cur:?node = option{MakeList(3)}
    loop:
        if (Q := Cur?):
            Print("node {Q.V}")
            set Cur = Q.Next
        else:
            break
    Print("{MakeT("t").Name}")
