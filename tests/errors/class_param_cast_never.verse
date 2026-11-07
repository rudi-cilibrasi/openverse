# expect: so intbox[…] would always fail
base(t:type) := class:
    Value:t
intbox := class(base(int)):
    Tag:int = 0
Main():void =
    B := base(string){Value := "x"}
    if (I := intbox[B]) then Print("no")
