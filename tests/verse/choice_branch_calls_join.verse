# An if with calls with several values in its branches (#283), where the
# first success is taken, with no type written: its branches' join, as for
# any if; for `set L = if …`, at L's type
Opt(N : int):?int = option{N} | false
Two(N : int):int = N | N + 10
Main()<transacts>:void =
    if (Z := (if (1 = 1) then Opt(4) else false), V := Z?) then Print("a {V}")
    if (Z := (if (1 = 2) then Opt(4) else false)) then Print("b {if (Z?) then 1 else 0}")
    if (Z := (if (1 = 1) then Two(4) else 2.5)) then Print("c")
    var O : ?int = false
    if (set O = (if (1 = 1) then Opt(4) else false), V := O?) then Print("d {V}")
    if (set O = (if (1 = 2) then Opt(4) else false), V := O?) then Print("never") else Print("e")
    Print("o {if (V := O?) then V else 0}")
