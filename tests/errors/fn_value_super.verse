# expect: (super:)Name cannot be used as a value
p := class:
    Name():string = "p"
q := class(p):
    Name<override>():string =
        Parent:type{_():string} = (super:)Name
        "q"
Main():void = Print("x")
