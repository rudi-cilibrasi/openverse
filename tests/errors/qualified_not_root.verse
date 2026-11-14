# expect: (j:)M: j's M overrides another; qualify it with the interface that introduces M, (i:)
i := interface:
    M():int
j := class<abstract>(i):
    M<override>():int = 5
c := class(j):
    (j:)M<override>():int = 1
Main():void = Print("x")
