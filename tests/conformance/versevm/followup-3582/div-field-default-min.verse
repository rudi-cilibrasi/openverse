# 3582 follow-up (#724), compile only: a field default that calls the
# built-in Min (no function of the program's): whether field defaults treat
# built-ins as module constants do (div-const-intrinsic). OpenVerse refuses
# it: "the default of field 'Size' of thing calls Min" (3582).
thing := class:
    Size:int = Min(3, 7)

Main():void =
    T := thing{}
    Print("OVPROBE size {T.Size}")
