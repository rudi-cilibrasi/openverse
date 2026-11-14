# expect: an int is an any, but not as it is: an any holds no value in openverse
covariant_class(t:type) := class:
    Data:t
Main():void =
    X:covariant_class(any) = covariant_class(int){Data := 1}
