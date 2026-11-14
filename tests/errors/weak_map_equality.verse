# expect: an operand of '=' must be comparable, and weak_map(int, int) is a weak_map
Main():void =
    W:weak_map(int, int) = map{1 => 2}
    V:weak_map(int, int) = map{1 => 2}
    if (W = V) { Print("equal") }
