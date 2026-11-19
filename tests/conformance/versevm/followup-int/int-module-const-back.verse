# Follow-up (#724): a module constant whose value is in range but whose
# evaluation leaves it on the way. OpenVerse refuses it at compile time
# (integer add overflow), as it reads Epic's 9003 for
# book-int-pow64-module-const; admitted, it would print "back to max".
Back:int = (9223372036854775807 + 1) - 1

Main():void =
    if (Back = 9223372036854775807) then Print("OVPROBE back to max") else Print("OVPROBE not max")
