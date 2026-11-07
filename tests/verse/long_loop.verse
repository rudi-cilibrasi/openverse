# A loop runs in constant native stack (#97). The next iteration of a loop,
# the right of a sequence and the branches of an if are tail positions: the
# depth bound of `openverse run` does not count them, because the compiled
# interpreter runs them as a loop. 8 million nested iterations would
# overflow its stack, so this test fails if that ever stops being true.
Main():void =
    var I:int = 0
    loop:
        set I += 1
        if (I >= 8000000) then break
    Print("{I}")
