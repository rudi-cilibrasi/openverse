# expect: a top-level definition must start at column 0
box := class:
    X:int
    Read():int =
        Inner():int = X
        Inner()
Main():void = Print(box{X:=7}.Read())
