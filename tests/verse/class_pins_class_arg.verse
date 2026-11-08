# classes that fix a type argument to a class or an interface type (#142,
# review of #155: the prototype's type arguments must agree with the pins)
animal := class:
    Kind():string = "animal"
dog := class(animal):
    Kind<override>():string = "dog"
named := interface:
    Name():string
cat := class(named):
    Name<override>():string = "cat"
puppy := class(named):
    Name<override>():string = "puppy"
box(t:type) := class:
    V:t
    Get():t = V
an_box := class(box(animal)):
    Get<override>():animal = dog{}
n_box := class(box(named)):
    Get<override>():named = puppy{}
G(B:box(t) where t:type):t = B.Get()
Main():void =
    Print(G(an_box{V := animal{}}).Kind())
    Print(G(n_box{V := cat{}}).Name())
    Print(G(box(animal){V := animal{}}).Kind())
