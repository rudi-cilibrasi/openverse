# Access specifiers where the Book allows them (Book of Verse ch. 12, docs/research/access-specifiers.md):
# a module and its definitions <public>, <internal> or <epic_internal>; a class's and an interface's
# members any of the six; a class's constructor <protected>; a struct's fields <public>, and <final>.
Geometry<public> := module:
    point<public> := struct<internal>:
        X<public>:int = 0
        Y<final>:int = 0
    Origin<epic_internal>:int = 1
    MakePoint<public>(X:int):point = point{X := X + Origin}
base<public> := class<protected>:
    Size<protected>:int = 3
    Hidden<private>():int = Size * 2
    Shown<public>():int = Hidden()
derived := class(base):
    Size<override>:int = 5
    Read<internal>():int = Size
Main():void =
    D := derived{}
    Print("{Geometry.MakePoint(7).X} {D.Shown()} {D.Read()}")

