# expect: expected int, found char (the default of ?A in a function type
# Also in a parameter written as a signature (Book DefaultNamed tests, #503)
F1(F(?A:int = 'a'):int):int = F(?A := 2)
G(?A:int = 0):int = A
Main():void =
    Print("{F1(G)}")
