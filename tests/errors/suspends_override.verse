# expect: b.Run must be <suspends>, as a.Run, which it overrides, is
a := class:
    Run()<suspends>:void = Sleep(1.0)
b := class(a):
    Run<override>():void = {}
Main():void = Print("x")
