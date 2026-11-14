# expect: a weak_map key must be comparable, and any is not
Main():void =
    W:weak_map(any, int) = map{}
