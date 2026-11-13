# expect: 3:4: a constant in a module needs its type: write Limit:t = …
config := module:
    Limit := Max
    Max:int = 10
Main():void = {}
