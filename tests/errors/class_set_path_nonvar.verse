# expect: field 'Count' of class counter is not a var
# Through an alias in a struct, a non-var field still cannot be set.
counter := class:
    Count:int = 0
holder := struct:
    C:counter
Main():void =
    H := holder{C := counter{}}
    set H.C.Count = 1
