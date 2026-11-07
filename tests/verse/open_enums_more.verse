# open enums (#76 review): braced syntax, <persistable>, a case in an if
# condition and nested cases, and an open enum from an imported file
using{"lib/open_enum_lib"}

dir := enum<open>{North, South}
mode := enum<closed><persistable>{On, Off}

Both(D:dir, M:mode):string = case (D):
    dir.North => case (M):
        mode.On => "north on"
        mode.Off => "north off"
    _ => case (M):
        mode.On => "other on"
        _ => "other off"

Main():void =
    Print(Both(dir.North, mode.Off))
    Print(Both(dir.South, mode.On))
    if (X := case (dir.South):
            dir.North => 1
            dir.South => 2) then Print("{X}")
    I := imported.Q
    Print(case (I):
        imported.P => "p"
        _ => "q")
