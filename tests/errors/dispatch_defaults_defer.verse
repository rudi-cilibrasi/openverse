# expect: spawn in a defer
Work()<suspends>:int=1
base(t:type) := interface:
    F(?T:task(int)):int
ib := class(base(int)):
    F<override>(?T:task(int)=spawn{Work()}):int=1
Run(P:base(a) where a:type):void=
    defer:Print("{P.F()}")
    Print("end")
Main():void=Run(ib{})
