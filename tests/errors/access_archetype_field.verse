# expect: the field Seed of rng is <private>: only rng's own code may use it
# (a field given in a construction is read there: Book of Verse ch. 12, example 15)
rng := class:
    Seed<private>:int = 1
    Next<public>():int = Seed * 7
Main():void = Print("{rng{Seed := 3}.Next()}")
