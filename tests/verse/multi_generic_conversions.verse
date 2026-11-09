# a generic function with several values whose arguments convert to its parameters' types: a tuple to an array, false to an empty option, array{} at the type the others give (#235, review of #282)
Both(X:[]t where t:type)<decides>:t = X[0] | X[1]
Opt(X:?t, Y:t where t:type)<decides>:t = (X?) | Y
Firsts(X:t, Ys:[]t where t:type)<decides>:t = X | Ys[0]
Main():void =
    for (Z := Both[(1, 2)]) { Print("both {Z}") }
    for (Z := Opt[false, 5]) { Print("opt {Z}") }
    for (Z := Firsts[3, array{}]) { Print("firsts {Z}") }
