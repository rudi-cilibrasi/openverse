# a named parameter's default may use the parameters before it (Book of
# Verse ch. 6), defaults before it included; a method's sees its fields

F(X:int, ?Y:int = X * 2):int = X + Y

Range(Lo:int, ?Hi:int = Lo + 10, ?Step:int = Hi - Lo):string = "{Lo}..{Hi} by {Step}"

Greet(Name:string, ?Greeting:string = "Hello", ?Line:string = "{Greeting}, {Name}!"):string = Line

counter := class:
    Base:int
    Add(N:int, ?By:int = N + Base):int = N + By

Main():void =
    Print("{F(3)} {F(3, ?Y := 1)}")
    Print(Range(0))
    Print(Range(0, ?Hi := 20))
    Print(Range(0, ?Step := 1))
    Print(Greet("Ada"))
    Print(Greet("Ada", ?Greeting := "Hi"))
    C := counter{Base := 100}
    Print("{C.Add(1)} {C.Add(1, ?By := 2)}")
