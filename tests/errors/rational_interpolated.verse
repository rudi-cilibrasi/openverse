# expect: 7:22: no ToString for rational
# A rational has no ToString (Book of Verse ch. 2, "ToString()": int,
# float, char and string; the API reference adds char32 and no rational),
# and interpolation calls ToString ("Interpolation works for any value that
# has a ToString() function in scope"), so a rational is refused in one,
# also where the source divides only there.
Main():void = Print("{if (X := 1 / 3) then X else 1 / 2}")
