# Book: Tests/Effects.versetest:490 refuses (3512) a <transacts> function
# calling one without specifiers; docs/13_effects.md describes the default as
# almost <transacts>.
F():void = {}
G()<transacts>:void = F()

Main():void =
    G()
    Print("OVPROBE called")
