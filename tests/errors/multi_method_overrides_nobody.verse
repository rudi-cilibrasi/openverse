# expect: 4:4: Sizes has no body: give it one, or make shape <abstract>
# (a body, in a class that is not abstract)
shape := class:
    Sizes()<transacts>:int
big := class(shape):
    Sizes<override>()<transacts>:int = 1 | 2
Main()<transacts>:void =
    for (V := shape{}.Sizes()):
        Print("{V}")
    Print("done")
