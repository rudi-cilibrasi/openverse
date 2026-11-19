# expect: 4:37: a cast to int takes an int, found c (Epic's Verse compiler, UEFN 43.12: error 3509)
# int[X] of a class's value is refused (the Book of Verse's tests, Cast.versetest:35, 3509)
c := class{}
F(C:c)<transacts><decides>:void = int[C]
Main():void = {}
