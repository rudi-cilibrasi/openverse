# expect: a constant at the top level needs its type: write Again:t = …
# X := Y, with Y a constant, is no type alias, so it is a constant without its type (Book of Verse ch. 16).
Count:int = 7
Again := Count
Main():void = Print("{Again}")
