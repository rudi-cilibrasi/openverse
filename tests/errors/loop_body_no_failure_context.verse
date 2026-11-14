# expect: a loop's body is none, also in a <decides> function
F(X:?int)<decides>:int =
    loop:
        X?
        break
    1
Main():void = {}
