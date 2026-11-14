# A type as a value (of a metatype) is no object of the program's classes:
# F(:subtype(c)) and F(:d) are two overloads a call tells apart, and a
# module's function may take the name of one around it with such disjoint
# parameters (Book of Verse ch. 10, "Shadowing and Qualification"; the
# Book's tests, ParametricTypes.versetest 45 and 717-723).
c := class {}
d := class:
    X:int = 2
F(:subtype(c)):string = "type"
F(D:d):string = "object {D.X}"
m := module:
    G<public>(:subtype(c)):string = "m.type"
G(D:d):string = "object"
Main():void =
    Print("{F(c)} {F(d{})} {m.G(c)} {G(d{})}")
