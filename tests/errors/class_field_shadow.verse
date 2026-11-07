# expect: 'Step' is already a field or method of counter
counter := class:
    Step:int = 1
    Next():int =
        Step := 7
        Step
Main():void = Print("{counter{}.Next()}")
