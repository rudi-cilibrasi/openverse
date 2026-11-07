# expect: 5:27: m.sub is internal to m: mark it <public> to use it outside
m := module:
    sub := module:
        Deep<public>:int = 3
Main():void = Print("{m.sub.Deep}")
