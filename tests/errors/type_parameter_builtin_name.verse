# expect: 4:17: 'char32' is the name of a built-in type
# A type parameter does not take a built-in type's name, char32 as int: a
# use of it would read the built-in type.
F(X:char32 where char32:type):char32 = X
Main():void = Print("{F(1)}")
