# A module's constant has no side effect (Book of Verse tests,
# DefaultValueAssignment.versetest:199): its value may construct <computes>
# classes and structs and use operators and the converging built-ins, but
# call no function of the program's (Epic's Verse compiler, UEFN 43.12,
# error 3582, #724: tests/errors/initializer_convergence_constant_call).
point := struct<computes>{ X:int = 0, Y:int = 0 }
shape := class<computes>{ Sides:int = 3 }
Origin:point = point{}
Square:shape = shape{ Sides := 2 * 2 }
Ten:int = Abs(-10)
Main():void = Print("{Origin.X} {Square.Sides} {Ten}")
