# expect: every class below named (ints) fixes type arguments that named(t) does not have, so none can be it
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
