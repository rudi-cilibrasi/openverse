# defer (#82 review): a scope whose value is a logic query; a defer body
# that declares locals, including one named like a later local of the scope
# (the body sees the locals where it was registered); a branch that is only
# a defer; X := B? at type logic (Core's checker)
F(B:logic)<decides>:void =
    defer:
        Print("d")
    B?

G(B:logic):int =
    defer:
        Z := 10
        Print("defer Z={Z}")
    Z := 3
    if (B?):
        return Z
    Z + 1

Main():void =
    if (F[true]) then Print("ok")
    if (F[false]) then Print("no") else Print("failed")
    Print("{G(true)}")
    Print("{G(false)}")
    if (1 = 1) then defer{Print("x")}
    B:logic = true
    if (X := B?) then Print("query ok")
    Print("y")
