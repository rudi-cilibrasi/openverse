# expect: 4:23: m.Hidden is internal to m: mark it <public> to use it outside
m := module:
    Hidden:int = 1
Main():void = Print("{m.Hidden}")
