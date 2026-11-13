# expect: point is <concrete>, so its field 'Y' needs a default
point := struct<concrete>:
    X:int = 0
    Y:int
Main():void = {}
