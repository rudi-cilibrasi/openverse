# Book: Tests/Effects.versetest:551 refuses (3512) a class block calling a
# function without specifiers.
F():void = {}
c := class {block{F()}}

Main():void =
    Print("OVPROBE compiled")
