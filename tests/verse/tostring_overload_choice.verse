tag := struct:
    Code:int

ToString(T:tag)<computes>:string = "left {T.Code}" | "right {T.Code}"

Main():void =
    for (Text := "pick {tag{Code:=3}}"):
        Print(Text)
