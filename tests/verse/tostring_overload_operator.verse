parcel := class<unique>:
    var Visits:int = 0

ToString(P:parcel)<transacts>:parcel =
    set P.Visits += 1
    P

operator'+'(Prefix:string, P:parcel)<transacts>:parcel =
    Print(Prefix)
    set P.Visits += 10
    P

Main():void =
    P := parcel{}
    Result := "parcel {P}"
    if (Result = P) then Print("same object")
    Print("visits {P.Visits}")
    Again := "{ToString(P)}"
    if (Again = P) then Print("explicit and implicit")
    Print("visits {P.Visits}")
