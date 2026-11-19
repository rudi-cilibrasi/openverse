# Asks the same of two interfaces, ii and II. OpenVerse refuses it (#724).
# If Epic admits it, it prints
#   defined
ii := interface:
    Get():int = 1

II := interface:
    Get():int = 2

Main():void =
    Print("OVPROBE defined")
