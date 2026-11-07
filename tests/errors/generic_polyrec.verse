# expect: Grow is instantiated at ever larger types (polymorphic recursion is not supported)
Grow(X:t, N:int where t:type):int =
    if (N > 0) then Grow((X, X), N - 1) else 0

Main():void = Print("{Grow(1, 3)}")
