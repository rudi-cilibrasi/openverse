# Control for int-module-const-back: every step in range. Both admit it and
# print "max".
Back:int = (9223372036854775806 + 1) - 0

Main():void =
    if (Back = 9223372036854775807) then Print("OVPROBE max") else Print("OVPROBE not max")
