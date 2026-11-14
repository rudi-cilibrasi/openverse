# modules (#112): a class hierarchy, a constructor, generics and overloads across modules
shapes := module:
    shape<public> := class<abstract>:
        Area<public>():int
    Twice<public>(X:t where t:type):tuple(t, t) = (X, X)
    Show<public>(X:int):string = "int {X}"
    Show<public>(X:string):string = "string {X}"
    point<public> := struct<computes>:
        X<public>:int = 0
        Y<public>:int = 0

geometry := module:
    using{shapes}
    square<public> := class(shape):
        Side<public>:int
        Area<override>():int = Side * Side
    MakeSquare<public><constructor>(S:int) := square:
        Side := S
    Total<public>(Ss:[]shape):int =
        var T:int = 0
        for (S : Ss) { set T += S.Area() }
        T
    Origin<public>:point = point{X := 1, Y := 2}

Main():void =
    Sq := geometry.MakeSquare(3)
    Print("{Sq.Area()} {geometry.Total(array{Sq, geometry.square{Side := 2}})}")
    P := shapes.Twice(5)
    Print("{P(0)} {P(1)}")
    Print(shapes.Show(1))
    Print(shapes.Show("a"))
    O := geometry.Origin
    Print("{O.X} {O.Y}")
    Q:shapes.point = shapes.point{Y := 7}
    Print("{Q.Y}")
