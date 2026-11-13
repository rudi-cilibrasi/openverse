# expect: (d:)F: a second method F beside the one d inherits
base := class:
    F():int = 1
d := class(base):
    (d:)F():int = 2
Main():void = {}
