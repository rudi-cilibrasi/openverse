# a block that constructs its own class (#41 review): its effects are those
# of its code, found from none, within its declared construction budget
rec := class<computes>:
    D:int
    block:
        Print("rec {D}")
        if (D < 2):
            R := rec{D := D + 1}
Make()<computes>:rec = rec{D := 0}
Main():void = Print("{Make().D}")
