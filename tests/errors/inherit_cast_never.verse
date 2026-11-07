# expect: so fish[…] would always fail
animal := class:
    N:int = 0
fish := class(animal):
    F:int = 0
dog := class(animal):
    D:int = 0
Main():void =
    X := dog{}
    if (Y := fish[X]) then Print("no")
