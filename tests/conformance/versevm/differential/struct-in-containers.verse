# Structs inside arrays and maps: replacing an element, and a struct as a map
# key found by an equal struct made later.
# Tests LANGUAGE.md, Maps: "a comparable key ... through ... a struct's
# fields"; Structs: structural equality. (Epic agrees on a struct key with
# an option field: fingerprint/vm-map-struct-option-key.)
# OpenVerse prints (Lean and C agree):
#   9 1 c 2
cell2 := struct:
    R:int
    C:int

Main():void =
    var Cells:[]cell2 = array{cell2{R := 0, C := 0}, cell2{R := 1, C := 1}}
    Old := Cells
    if (set Cells[1] = cell2{R := 9, C := 9}) {}
    var Grid:[cell2]string = map{cell2{R := 0, C := 1} => "a"}
    if (set Grid[cell2{R := 2, C := 2}] = "b", set Grid[cell2{R := 0, C := 1}] = "c") {}
    if (N := Cells[1], O := Old[1], G := Grid[cell2{R := 0, C := 1}]):
        Print("OVPROBE {N.R} {O.R} {G} {Grid.Length}")
