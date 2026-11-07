# expect: interface named takes no type arguments
named := interface:
    Name():string = "d"
sub := class(named(int)):
    Y:int = 0
Main():void = Print("x")
