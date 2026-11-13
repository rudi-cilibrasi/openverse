# In a <suspends> function, a value kept across a suspension point has its
# type inferred when its code is lowered (#188): a for's values, or its
# source, that are empty literals take the type they are checked against.
F()<suspends>:void =
    Words := for (I := 1..2) { Sleep(0.01); "" }
    Print("{Words.Length}")
    Print("{(for (I := 1..3) { Sleep(0.01); if (false?) then "x" else "" }).Length}")
    Grid := for (I := 1..2, J := 1..2) { Sleep(0.01); "" }
    Print("{Grid.Length}")
    for (C : "") { Sleep(0.01); Print("never") }
    for (C : (if (false?) then "x" else "")) { Sleep(0.01); Print("never") }
    for (I := 1..2) { Sleep(0.01); "" }
    Sleep(0.01)
    Print("{(if (false?) then "x" else "").Length} {"".Length}")
Main()<suspends>:void =
    F()
