# expect: a top-level definition must start at column 0
# Unsupported declarations are refused even when not called.
Unused():void =
    Inner():int = 7
    Print("unused")
Main():void = Print("main")
