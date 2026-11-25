# 3582 follow-up (#724), compile only: a module constant defined by
# option{...} of a literal. OpenVerse admits it and prints "value 3".
Maybe:?int = option{3}

Main():void =
    if (V := Maybe?) then Print("OVPROBE value {V}") else Print("OVPROBE empty")
