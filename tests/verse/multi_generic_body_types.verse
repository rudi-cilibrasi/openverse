# a generic function with several values that writes a type mentioning its type parameter in its body: renamed for the site, at the type its arguments give (#235)
Twice(X:t where t:type):t =
    Y:t = X
    Y | X
Main():void =
    for (Z := Twice(1)) { Print("{Z}") }
