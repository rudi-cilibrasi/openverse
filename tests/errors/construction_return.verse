# expect: a return cannot leave a construction's field value
c := class{ A:int }
F(N:int):int =
    X := c{ A := block{ if (N < 0) { return 0 }; N } }
    X.A
Main():void = Print("{F(1)}")
