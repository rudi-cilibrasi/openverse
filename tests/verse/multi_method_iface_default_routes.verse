# Interface defaults of methods with several values when a class has two
# routes (#375's review): its parent class's own implementation wins over a
# default of an interface it lists, in either declaration order; and
# (super:) reaches the nearest default, the derived interface's
shape := interface:
    Sides()<transacts>:int = 1 | 2
deep := interface(shape):
    Sides<override>()<transacts>:int = 50 | 51
tri := class(shape):
    Sides<override>()<transacts>:int = 3 | 4
kid := class(tri, deep):
    X : int = 0
plain := class(shape):
    Q : int = 0
bare := class(plain, deep):
    Sides<override>()<transacts>:int = (super:)Sides() + 1000
lone := class(plain, deep):
    Z : int = 0
Main()<transacts>:void =
    Ss : []shape = array{kid{}, bare{}, lone{}, plain{}}
    for (S : Ss, N := S.Sides()):
        Print("a {N}")
