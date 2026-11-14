# Named arguments come after the positional ones (Book of Verse ch. 6), and
# only a named parameter has a default; a construction's field value may
# loop and break inside itself (Book of Verse tests, Constructor.versetest).
Subtract(A:int, ?B:int = 0, ?C:int = 0):int = A - B - C
c := class{ A:int }
Main():void =
    Print("{Subtract(42)} {Subtract(42, ?B := 1)} {Subtract(42, ?C := 2, ?B := 1)}")
    X := c{ A := block{ var I:int = 0; loop { set I += 1; if (I = 3) { break } }; I } }
    Print("{X.A}")
    if (V := option{1}?) then Print("{V}")
