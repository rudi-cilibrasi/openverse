# expect: class counter has no method 'Reset'
counter := class:
    N:int = 0

Main():void =
    C := counter{}
    C.Reset()
