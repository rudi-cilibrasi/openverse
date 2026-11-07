# expect: Look calls counter.Bump, which has the effect <writes>, which its effects (<reads>) do not allow
counter := class:
    var Count:int = 0
    Bump()<transacts>:void = set Count += 1
Look(C:counter)<reads>:void = C.Bump()
Main():void = Look(counter{})
