# expect: 4:24: char has no method 'ToCodePoint'
# ToCodePoint is a char32's; a char has ToCodeUnit.
Main():void =
    N := 'a'.ToCodePoint()
