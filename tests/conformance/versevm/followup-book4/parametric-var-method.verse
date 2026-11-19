# Edge of the 3552 rule (#724): a method of another class with an implicit
# type parameter of its own, Use(X:c(u) where u:type). OpenVerse refuses it
# as it does a function. If Epic admits it, it prints
#   result 1
c(t:type) := class:
    var Data:t

user := class:
    Use(X:c(u) where u:type):int = 1

Main():void =
    Print("OVPROBE result {user{}.Use(c(int){Data := 1})}")
