# expect: s, a class below b, holds it in its field V
# A bivariant class with a subclass that uses its parameter: the Book has
# any b a b(player), but a reference to b(player) holding an s(entity) could
# be cast back to s(player).
entity := class:
    ID:int
player := class(entity):
    Name:string
b(t:type) := class:
    K:int
s(t:type) := class(b(t)):
    V:t
Main():void =
    Y:b(player) = s(entity){K := 1, V := entity{ID := 1}}
