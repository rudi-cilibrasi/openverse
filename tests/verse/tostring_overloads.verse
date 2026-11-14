label := class<computes>:
    Code:int

ToString(L:label)<computes>:string = "label {L.Code}"
ToString(A:int, B:int, ?Scale:int=1)<computes>:string = ToString((A+B)*Scale)

local_text := module:
    item<public> := class<computes>:
        Code<public>:int
    ToString<public>(I:item)<computes>:string = "local {I.Code}"
    Show<public>(I:item)<computes>:string = "[{I}] {ToString(9)}"

Main():void =
    Print(ToString(label{Code:=7}))
    Print("[{label{Code:=8}}]")
    Print("sum {2, 5}; scaled {2, 5, ?Scale:=3}")
    Print(ToString((3, 6)))
    Print("primitive {4} {1.5} {'x'} {0u79} {"text"}")
    Print(local_text.Show(local_text.item{Code:=11}))
    Print(local_text.ToString(12))
