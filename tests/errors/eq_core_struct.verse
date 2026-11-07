# expect: '=' compares values of different types, p and q
p := struct:
    C:int
q := struct:
    C:int
Main():void =
    if (p{C := 1} = q{C := 1}) {}
