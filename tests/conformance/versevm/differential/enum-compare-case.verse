# Enums: equality, case with every value and with a default, and an enum in
# an array searched with Find.
# Tests LANGUAGE.md, Supported, Enums: "equality, case that needs no _ when
# every value is named".
# OpenVerse prints (Lean and C agree):
#   N no | E yes | S no | W yes | eq y y find 2
dir := enum:
    North
    East
    South
    West

Name(D:dir):string =
    case (D):
        dir.North => "N"
        dir.East => "E"
        dir.South => "S"
        dir.West => "W"

Horizontal(D:dir):string =
    case (D):
        dir.East => "yes"
        dir.West => "yes"
        _ => "no"

Main():void =
    All:[]dir = array{dir.North, dir.East, dir.South, dir.West}
    for (D : All):
        Print("OVPROBE {Name(D)} {Horizontal(D)}")
    P := if (dir.North = dir.North) then "y" else "n"
    Q := if (dir.North <> dir.South) then "y" else "n"
    I := All.Find[dir.South] or -1
    Print("OVPROBE eq {P} {Q} find {I}")
