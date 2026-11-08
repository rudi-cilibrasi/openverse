# expect: 4:22: M.Hidden is internal to M: mark it <public> to use it outside
M := module:
    Hidden():int = 1
Main():void = Print("{(M:)Hidden()}")
