# Follow-up (#724): a module constant whose value is in range but whose
# evaluation leaves it on the way. OpenVerse refuses it at compile time
# (integer add overflow), and Epic does: 9003, "Runtime error while
# evaluating module". Admitted, it would print "back to max".
Back:int = (9223372036854775807 + 1) - 1

Main():void =
    if (Back = 9223372036854775807) then Print("OVPROBE back to max") else Print("OVPROBE not max")
