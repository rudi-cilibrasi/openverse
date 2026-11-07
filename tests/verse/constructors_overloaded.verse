# overloaded constructors (Book of Verse ch. 10): constructors of one name
# and class, taking disjoint parameters; a delegation, even to another
# overload of the name, is resolved by its arguments

player := class:
    Name:string
    Level:int = 1

MakePlayer<constructor>(N:string) := player:
    Name := N

MakePlayer<constructor>(N:string, L:int) := player:
    Name := N
    Level := L

MakePlayer<constructor>(L:int) := player:
    MakePlayer<constructor>("anon", L)

hero := class(player):
    Power:int

MakeHero<constructor>(N:string, P:int) := hero:
    Power := P
    MakePlayer<constructor>(N, P * 10)

MakeHero<constructor>(P:int) := hero:
    Power := P
    MakePlayer<constructor>("hero", P)

Main():void =
    A := MakePlayer("a")
    B := MakePlayer("b", 5)
    C := MakePlayer(7)
    Print("{A.Name} {A.Level} {B.Name} {B.Level} {C.Name} {C.Level}")
    H := MakeHero("h", 3)
    G := MakeHero(2)
    Print("{H.Name} {H.Level} {H.Power} {G.Name} {G.Level} {G.Power}")
