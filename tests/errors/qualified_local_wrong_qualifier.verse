# expect: (c:)X: a local is defined in the code it is written in, so its qualifier is (local:)
c := class:
    F():void =
        (c:)X:int = 0
Main():void = {}
