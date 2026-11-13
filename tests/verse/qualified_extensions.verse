# A qualifier selects among the extension methods in scope as among other
# names: X.(M:)F(…) is the extension method F of the module M.
Loud := module:
    (S:string).Shout<public>():string = "{S}!"
Quiet := module:
    (S:string).Shout<public>():string = "{S}."
    (N:int).Twice<public>():int = 2 * N
using{Loud}
using{Quiet}
Main():void =
    Print("{"a".(Loud:)Shout()} {"b".(Quiet:)Shout()} {(3).(Quiet:)Twice()}")
