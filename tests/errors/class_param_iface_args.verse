# expect: named takes 0 type argument(s), found 1
named := interface:
    Name():string = "d"
sub := class(named(int)):
    Y:int = 0
Main():void = Print("x")
