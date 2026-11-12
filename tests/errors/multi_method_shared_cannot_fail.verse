# expect: 7:4: the condition of this if cannot fail
a := class:
    Vals()<transacts>:int = 1 | 2
b := class:
    Vals()<transacts>:int = 7
Main()<transacts>:void =
    if (X := b{}.Vals()) { Print("never {X}") }
