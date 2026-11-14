# Every type parameter of a function is given by its parameters (the Book's
# tests, ParametricFunctions.versetest 336-378, 586, error 3503): named in a
# parameter's type where values go in, in the result's function type's
# parameters (a value out of which values go in), or in the bound of one
# that is; a type given as an argument gives it too (Book of Verse ch. 2,
# MaybeValueExplicit(t:type, ...)). A class that does not use its type
# parameter gives it, as an object holds its type arguments.
Drop(X:t where t:type):void = Print("dropped")
Sink(N:int where t:type):type{_(:t):void} = Drop
Up(X:t where t:subtype(u), u:type):t = X
Nothing(t:type):?t = false
tag(t:type) := class:
    Name:string
Named(T:tag(t), X:t where t:type):string = T.Name
Main():void =
    F:type{_(:int):void} = Sink(0)
    F(4)
    Print("{Up(5)}")
    O:?string = Nothing(string)
    if (not O?) then Print("nothing")
    Print(Named(tag(int){Name := "int tag"}, 3))
