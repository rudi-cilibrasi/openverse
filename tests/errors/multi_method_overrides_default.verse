# expect: 7:24: shape.Sizes has several values, so a call of it must be in a failure context that takes them: an if condition, a for's clauses, first{…}, option{…}, logic{…}, not, or the left of or (#235)
# (a call of an overridden method with several values in a default: refused as outside a failure context, not left to reach the stub)
shape := class:
    Sizes()<transacts>:int = 1 | 2
big := class(shape):
    Sizes<override>()<transacts>:int = 1000
G(?X : int = big{}.Sizes())<transacts>:int = X
Main()<transacts>:void =
    Print("{G()}")
    Print("{G(?X := 5)}")
