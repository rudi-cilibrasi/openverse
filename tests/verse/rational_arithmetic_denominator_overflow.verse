# A reduced denominator longer than the longest int is the overflow error
# (#724: a denominator past 64 bits is an int, int_verse_vm_rational)
# The longest int, 2^(2^20) - 1: one more is the overflow error (#724).
MaxInt()<computes>:int =
    var H:int = 2
    for (I := 1..19):
        set H *= H
    (H - 1) * (H + 1)
Main():void=
    if(V:=1/MaxInt()):
        Print("before")
        if(R:=V/2)then Print("{Floor(R)}")else Print("bad")
