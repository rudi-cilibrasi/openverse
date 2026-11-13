# An empty literal ("", or false, array{} or map{} at an expected type) has
# every type of its shape in Verse Core, so its checker infers none for it,
# nor for an if, a case, a tuple, … whose values are such. Where Verse Core
# infers a type (the operand of .Length, an index or a projection, the left
# of a comparison), it gets the one it was elaborated at.
Pick(S:string)<decides>:string = { S.Length > 0; S }
Main():void =
    Print("{"".Length} {(if (false?) then "" else "").Length}")
    Print("{(if (false?) then "" else if (true?) then "" else "").Length}")
    Print("{(case (1) { 1 => ""; _ => "" }).Length} {(Print("s"); "").Length}")
    Print("{(Pick[""] or "").Length} {(if (false?) then "" else false).Length}")
    # (an index, a projection, interpolation alone, concatenation, an array)
    if (C := (if (false?) then "" else "")[0]) then Print("{C}") else Print("no index")
    Print("[{("", 1)(0)}] {("", 1)(1)} {"{""}".Length} {("" + "").Length}")
    Print("{array{"", "x"}.Length} {("" + array{}).Length}")
    if (V := option{""}?) then Print("[{V}]")
    # (comparisons in conditions, whose value is inferred)
    if ("" = "") then Print("eq")
    if ((if (false?) then "" else "") <> "a") then Print("ne")
    if (not "" = "a") then Print("not")
    if (logic{"" = ""}?) then Print("logic")
    if ("" = "" and true?) then Print("and")
    # (a value of type any)
    A:any = ""
    B:any = if (false?) then "" else ""
    Print("any")
