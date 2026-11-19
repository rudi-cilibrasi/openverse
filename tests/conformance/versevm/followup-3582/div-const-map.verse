# 3582 follow-up (#724), compile only: a module constant defined by a map
# literal. OpenVerse admits it and prints "a 1".
Ages:[string]int = map{"a" => 1}

Main():void =
    if (A := Ages["a"]) then Print("OVPROBE a {A}") else Print("OVPROBE missing")
