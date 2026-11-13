# Defaults written in function types (#503): not part of the type and never
# run (a call that omits the parameter runs the function's own default), but
# checked at the parameter's type, with literals and top-level names, wherever
# the type is written: a local, a parameter, a signature parameter, a field,
# a module's definition.
Limit:int = 5
F1(?A:int = 1):int = A
F2(?A:rational = 3):rational = A
holder := class:
    Fn:type{_(?A:int = Limit):int}
Use(F:type{_(?A:int = 0):int}):int = F()
Sig(F(?A:int = Limit + 1):int):int = F() + F(?A := 10)
M := module:
    Max<public>:int = 9
    Call<public>(F:type{_(?A:int = Max):int}):int = F()
Main():void =
    G:type{_(?A:int = 99):int} = F1
    R:type{_(?A:rational = 2):rational} = F2
    H := holder{Fn := F1}
    Print("{G()} {Floor(R())} {H.Fn()} {Use(F1)} {Sig(F1)} {M.Call(F1)}")
