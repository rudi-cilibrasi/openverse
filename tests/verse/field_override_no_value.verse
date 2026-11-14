# A field re-declared with <override> and no value has no default there:
# a construction gives it (Book of Verse ch. 10, "Overriding Members"; its
# tests, Attributes/override.versetest 29-47).
base := class:
    A:int = 2
    Show():string = "base {A}"
sub := class(base):
    A<override>:int
leaf := class(sub):
    A<override>:int = 5
named := interface:
    Name:string
person := class(named):
    Name<override>:string
Describe(B:base):string = B.Show()
Main():void =
    Print("{Describe(base{})} {Describe(sub{A := 3})} {Describe(leaf{})} {person{Name := "Ada"}.Name}")
