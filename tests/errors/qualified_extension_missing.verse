# expect: module Loud has no member Shout
Loud := module:
    F<public>():int = 1
Main():void = Print("{"a".(Loud:)Shout()}")
