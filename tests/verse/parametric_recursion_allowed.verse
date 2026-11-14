# What the Book's rule on recursive parametric types leaves (ch. 10,
# "Recursive Parametric Types"): a parametric class that names itself at its
# own type parameters, one that names another parametric class which does
# not name it back, and classes without type parameters that name each other.
list_node(t:type) := class:
    Value:t
    Next:?list_node(t) = false
pair_list(t:type, u:type) := class:
    First:t
    Second:u
    Rest:?pair_list(t, u) = false
holder(t:type) := class:
    Items:[]list_node(t) = array{}
ping := class:
    Pong:?pong = false
pong := class:
    Ping:?ping = false
Sum(L:?list_node(int)):int =
    if (N := L?) then N.Value + Sum(N.Next) else 0
Main():void =
    L := list_node(int){Value := 1, Next := option{list_node(int){Value := 2}}}
    P := pair_list(int, string){First := 1, Second := "a", Rest := option{pair_list(int, string){First := 2, Second := "b"}}}
    H := holder(int){Items := array{L}}
    Q := ping{Pong := option{pong{}}}
    Print("{Sum(option{L})} {P.Second}{if (R := P.Rest?) then R.Second else ""} {H.Items.Length} {if (Q.Pong?) then "pong" else "none"}")
