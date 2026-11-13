# Empty literals as a choice's alternatives, and in functions with several
# values (#235), plain, recursive or taken lazily (#246): where Verse Core
# infers their type, each gets the one it was elaborated at.
Strs():string = "" | ""
Lens():int = ("" | "a").Length
Down(N:int):int =
    if (N > 0, "" = ""):
        ""
        N | Down(N - 1)
    else:
        0
Words(N:int):string = if (N > 0) then ("" | Words(N - 1)) else ""
Main():void =
    for (N := ("" | "").Length) { Print("choice {N}") }
    for (S := Strs(), N := S.Length) { Print("strs {N}") }
    for (N := Strs().Length) { Print("call {N}") }
    for (N := Lens()) { Print("lens {N}") }
    for (N := Down(2)) { Print("down {N}") }
    for (W := Words(2)) { Print("words [{W}] {W.Length}") }
    for (N := Words(1).Length, ("" | "a") = "") { Print("words {N}") }
    if (N := first{("" | "a")}.Length) then Print("first {N}")
