# expect: 3:0: the receiver of an extension method is one parameter, (Name:type) or (:type), not a named one or one with a default
# The receiver of an extension method is one positional parameter
(?X:int).Get():int = X
Main():void = {}
