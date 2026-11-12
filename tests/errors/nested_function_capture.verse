# expect: a top-level definition must start at column 0
# Local functions remain unsupported, including immutable captures.
Outer(X:int):int =
    Inner():int = X
    Inner()
Main():void = Print(Outer(7))
