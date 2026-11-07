# expect: a map key must be comparable, and counter is a class
counter := class:
    N:int = 0

Main():void =
    M:[counter]int = map{}
