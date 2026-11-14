# A module's constant has no side effect (Book of Verse tests,
# DefaultValueAssignment.versetest:199): its value may call <computes> and
# <reads> functions and construct <computes> classes and structs.
point := struct<computes>{ X:int = 0, Y:int = 0 }
shape := class<computes>{ Sides:int = 3 }
Double(N:int)<computes>:int = 2 * N
Origin:point = point{}
Square:shape = shape{ Sides := Double(2) }
Ten:int = Double(5)
Main():void = Print("{Origin.X} {Square.Sides} {Ten}")
