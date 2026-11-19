# 3582 follow-up (#724), compile only: a module constant defined by an enum
# value. OpenVerse admits it and prints "green".
color := enum:
    Red
    Green

Favourite:color = color.Green

Main():void =
    if (Favourite = color.Green) then Print("OVPROBE green") else Print("OVPROBE other")
