# expect: (super:)Name cannot be used as a value
p := class:
    Name():string = "p"
q := class(p):
    Name<override>():string = "q"
    Parent():type{_():string} = (super:)Name
Main():void = Print("x")
