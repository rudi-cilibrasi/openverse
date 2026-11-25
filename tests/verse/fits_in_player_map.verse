# FitsInPlayerMap (#724; the Book's Runtime API reference:
# FitsInPlayerMap(Value:t where t:subtype(persistable))<converges><reads><decides>:t;
# UEFN 43.12 admits and runs it, followup-refused/fits-in-player-map): the
# value, of a type that persists; it always succeeds in openverse
# (LANGUAGE.md, "Random numbers, the clock and the player map"). It is
# <converges>, so a data member's definition may call it.
color := enum<persistable>{Red, Green}
pt := struct<persistable>:
    X:int = 0
Kept:?int = option{FitsInPlayerMap[7]}
Check(N:int)<reads><decides>:int = FitsInPlayerMap[N]
Main():void =
    X:int = 5
    if (Y := FitsInPlayerMap[X]) then Print("fits {Y}")
    if (S := FitsInPlayerMap["abc"], P := FitsInPlayerMap[pt{X := 2}], E := FitsInPlayerMap[color.Green], O := FitsInPlayerMap[option{1.5}], V := O?):
        Print("{S} {P.X} {if (E = color.Green) then "green" else "red"} {V}")
    if (M := FitsInPlayerMap[map{1 => array{(2, true)}}], A := M[1], T := A[0]) then Print("{T(0)}")
    if (K := Kept?, C := Check[K]) then Print("{C}")
