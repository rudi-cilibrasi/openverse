# expect: the type parameter t of MakeEmpty appears in none of its parameters
box(t:type) := class:
    Value:t
MakeEmpty<constructor>(where t:type) := box(?t):
    Value := false
Main():void = Print("x")
