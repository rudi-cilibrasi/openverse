# A cast to a class no class of the value's is below compiles, warns, and
# fails when it runs (Book of Verse ch. 11:
# "These casts succeed and return the casted value, failing if the value is
# not of" the type; the Book's tests, Interface.versetest 140, 150).
animal := class:
    N:int = 0
fish := class(animal):
    F:int = 0
dog := class(animal):
    D:int = 0
Main():void =
    X := dog{}
    if (Y := fish[X]) then Print("no") else Print("not a fish")
    Z:animal = X
    if (fish[Z]) then Print("no") else Print("an animal, not a fish")
