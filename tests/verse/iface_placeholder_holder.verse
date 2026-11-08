# an interface that declares fields, whose classes all fix its type argument, read through a field in generic code (#157)
named(t:type) := interface:
    Name:string
    Get():t
ints := class(named(int)):
    V:int
    Get<override>():int = V
holder(t:type) := class:
    N:named(t)
Run(H:holder(t) where t:type):t = H.N.Get()
Main():void = Print("{Run(holder(int){N := ints{Name := "i", V := 3}})}")
