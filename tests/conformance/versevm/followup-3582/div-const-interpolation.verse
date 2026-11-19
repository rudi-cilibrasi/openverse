# 3582 follow-up (#724), compile only: a module constant defined by a string
# that interpolates an int (no call written). OpenVerse reads interpolation
# as a call of ToString, and refuses it: "the value of the constant Text
# calls ToString (to interpolate an int)" (3582). If Epic admits it, the
# run prints "text base 6".
Base:int = 6
Text:string = "base {Base}"

Main():void =
    Print("OVPROBE text {Text}")
