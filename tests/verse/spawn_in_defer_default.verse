# A call in a defer whose callee's default spawns (#724, spawn_in_defer;
# refused before, "spawn in a defer"): the default is evaluated where the
# defer runs.
Work()<suspends>:int=1
base(t:type) := interface:
    F(?T:task(int)):int
ib := class(base(int)):
    F<override>(?T:task(int)=spawn{Work()}):int=1
Run(P:base(a) where a:type):void=
    defer:Print("{P.F()}")
    Print("end")
Main():void=Run(ib{})
