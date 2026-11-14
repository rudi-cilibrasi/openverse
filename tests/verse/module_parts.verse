# A module may be defined in parts, which are one module: each part's
# members are the module's, a later part sees an earlier one's and the
# parts' access levels agree (the Book of Verse's tests,
# Modules/PartialModuleDefinitions.versetest 157-176; ch. 16: a module's
# files share its namespace).
shapes<public> := module:
    square<public> := class:
        Side<public>:int = 2
    Area<public>(S:square):int = S.Side * S.Side
outer := module:
    (outer:)inner<public> := module:
        One<public>:int = 1
    inner<public> := module:
        Two<public>:int = One + 1
shapes<public> := module:
    Perimeter<public>(S:square):int = 4 * S.Side
    Both<public>(S:square):tuple(int, int) = (Area(S), Perimeter(S))
Main():void =
    S := shapes.square{}
    B := shapes.Both(S)
    Print("{shapes.Area(S)} {shapes.Perimeter(S)} {B(0)} {B(1)} {outer.inner.One} {outer.inner.Two}")
