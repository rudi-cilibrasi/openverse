# expect: weak_map(…) is a type, not a function
# weak_map.versetest:32 writes a type alias in a body; openverse has types as
# values for classes and interfaces only
Main():void =
    t := weak_map(int, int)
