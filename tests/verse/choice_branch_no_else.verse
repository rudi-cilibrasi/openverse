Test(N:int)<transacts><decides>:int =
    Print("cond {N}")
    N > 0
    N
Down(N:int):int = if (N > 0) then (N | Down(N - 1)) else 0
Inline():void =
    if (true?) then (Print("inline a") | Print("inline b"))
    Print("inline tail")
Repeat(N:int)<transacts>:void =
    if (N > 0) then (Print("repeat {N}") | Repeat(N - 1))
Ping(N:int)<transacts>:void =
    if (N > 0) then (Print("ping {N}") | Pong(N - 1))
Pong(N:int)<transacts>:void =
    if (N > 0) then Ping(N - 1)
Main()<transacts>:void =
    for (K := 0..1, if (N := Test[K]) then (Print("a {N}") | Print("b {N}"))):
        Print("item {K}")
    for (K := 0..1, V:void = if (K = 0) then Down(2)):
        Print("lazy {K}")
    for (K := 0..2, if (K = 0) then (Print("c") | Print("d")) else if (K = 1) then { X := 3 | 4; Print("block {X}") }):
        Print("chain {K}")
    for (if (false?) then (1 | 2) else if (true?) then 3) { Print("plain branch") }
    var N:int = 0
    if (if (K := Test[2]) then ((set N = K; Print("reject")) | (set N = K + 1; Print("keep"))), N > 2):
        Print("first {N}")
    if (if (true?) then (false? | false?)) then Print("wrong") else Print("no values")
    if (if (false?) then (Err() | Err())) then Print("implicit value")
    if (option{if (true?) then (Print("option first") | Err())}?) then Print("some void")
    if (if (true?) then Down(2)) then Print("first lazy")
    for (Inline()) { Print("inline value") }
    for (Repeat(2)) { Print("repeat value") }
    if (Repeat(2), false?) then Print("wrong") else Print("rollback")
    for (Ping(2)) { Print("group value") }
