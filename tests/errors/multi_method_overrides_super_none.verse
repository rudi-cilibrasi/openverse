# expect: 6:4: nothing above b implements 'M'
# ((super:)M() with nothing above implementing M: as for a method with one value)
a := class<abstract>:
    M()<transacts>:int
b := class(a):
    M<override>()<transacts>:int = (super:)M() | 2
Main()<transacts>:void =
    for (X := b{}.M()):
        Print("{X}")
