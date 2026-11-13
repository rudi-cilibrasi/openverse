# expect: ToString takes one argument
# `{2, 3}` in a string is ToString(2, 3) (Book of Verse tests, Literals/String.versetest:242)
Main():void = Print("abc {2, 3} def")
