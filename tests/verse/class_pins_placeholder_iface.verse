# an interface with fields borrows the placeholder of a class below it (#157)
named(t:type) := interface:
    Name:string
    Get():t
base(t:type) := class<abstract>(named(t)):
    V:t
ib := class(base(int)):
    Get<override>():int = V
GetN(N:named(t) where t:type):t = N.Get()
First(Bs:[]base(t), D:t where t:type):t = if (B := Bs[0]) then GetN(B) else D
Main():void = Print("{First(array{ib{Name := "i", V := 3}}, 0)}")
