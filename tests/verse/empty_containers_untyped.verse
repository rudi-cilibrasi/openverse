# An array{} or map{} with no type from its context is an array (a map) of
# false, the type below every type, which converts to every array (map)
# type (Book of Verse tests: Array.versetest 90, 154; ArrayRemove.versetest:7;
# Concatenate.versetest 4-8; String.versetest:181; BinaryAddString.versetest:23;
# for.versetest:114; Map.versetest:236).
Main():void =
    A1 := array{}
    A2 := A1 + array{1}
    if (A2 = array{1}) then Print("A2 {A2.Length}")
    if (array{}.Remove[0, 0] = array{}) then Print("remove")
    X := array{}
    if (X = "") then Print("empty string")
    if (array{} + "" = "") then Print("plus string")
    if (Concatenate(array{}) = array{}, Concatenate() = array{}) then Print("concatenate")
    B := for (Y : array{}, Z : array{1}) { Y + Z }
    if (B = array{}) then Print("for {B.Length}")
    M := map{}
    if (M = map{}) then Print("map {M.Length}")
    if (not array{}.Last[]) then Print("no last")
    I:[]int = array{} + array{2}
    Print("{I.Length}")
