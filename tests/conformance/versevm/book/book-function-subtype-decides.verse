# Book: Tests/FunctionTypes.versetest:191 refuses (3509) a function without
# <decides> where a <transacts><decides> function is expected.
f19():int = return 1
f24(g()<transacts><decides>:int):int = return g[] or 3
test():void = f24(f19)

Main():void =
    test()
    Print("OVPROBE called")
