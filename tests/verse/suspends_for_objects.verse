# a for over objects of a parametric class in a suspends function, as a
# statement and as a value, across suspension points: its element slot
# lives in the frame (no placeholder per resumption) (#156)
cell(t:type) := class:
    V:t
Main()<suspends>:void =
    Cs := array{cell(int){V := 1}, cell(int){V := 2}, cell(int){V := 3}}
    var S:int = 0
    var I:int = 0
    loop:
        if (I >= 2000) then break
        set I += 1
        for (C : Cs) do set S += C.V
        Sleep(0.01)
    Ds := for (C : Cs, C.V <> 2):
        Sleep(0.01)
        cell(int){V := C.V * 10}
    Es := for (D : Ds) { D.V + 1 }
    Print("{S} {Ds.Length} {Es.Length}")
    for (E : Es) { Print("{E}") }
