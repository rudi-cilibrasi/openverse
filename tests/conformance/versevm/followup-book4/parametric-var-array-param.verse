# Edge of the 3552 rule (#724): F(X:[]c(t) where t:type), the class inside
# an array type. OpenVerse finds the class anywhere in the type and refuses
# it. If Epic admits it, it prints
#   length 1
c(t:type) := class:
    var Data:t

F(X:[]c(t) where t:type):int = X.Length

Main():void =
    Print("OVPROBE length {F(array{c(int){Data := 1}})}")
