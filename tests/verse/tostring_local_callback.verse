label := class<computes>:
    Code:int

Render(L:label)<computes>:string = "local {L.Code}"

Show(ToString(:label)<computes>:string, L:label)<computes>:string =
    "callback {L}"

Main():void = Print(Show(Render, label{Code:=17}))
