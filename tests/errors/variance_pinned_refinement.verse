# expect: pcell, a class below cell, fixes it
# A class that fixes a covariant parameter, cast to in code generic over the
# parent: the cast refines t := player, which a cell(entity) holding a pcell
# would make false (docs/research/variance.md, "Pins").
entity := class:
    ID:int
player := class(entity):
    Name:string
cell(t:type) := class:
    V:t
pcell := class(cell(player)):
    K:int = 0
box(t:type) := class:
    var B:t
F(C:cell(t), Bx:box(t) where t:type):void =
    if (P := pcell[C]):
        X:player = Bx.B
        Print(X.Name)
Main():void =
    C:cell(entity) = pcell{V := player{ID := 1, Name := "p"}}
    F(C, box(entity){B := entity{ID := 2}})
