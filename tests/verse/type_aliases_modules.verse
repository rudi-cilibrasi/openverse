# Type aliases in modules: a module's alias is its member, `<public>` to be
# used outside it, as `M.point`; module data states its type, an alias is no
# data
geometry := module:
    point<public> := tuple(int, int)
    coordinate := int
    Twice<public>(X:coordinate):coordinate = X + X
    Origin<public>:point = (0, 0)
    shape<public> := class:
        Sides:int = 3
    figure<public> := shape

Main():void =
    P:geometry.point = (1, 2)
    Print("{P(0) + P(1)} {geometry.Twice(21)} {geometry.Origin(0)}")
    F:geometry.figure = geometry.figure{}
    Print("{F.Sides}")
