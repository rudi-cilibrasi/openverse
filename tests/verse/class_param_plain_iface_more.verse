# a parametric class below a non-parametric interface, and a class adding a
# type parameter below a parametric interface's implementation: both supported
# since #278 and #308 (LANGUAGE.md listed them as not yet supported)
shower := interface:
    Show():string
box(t:type) := class(shower):
    V:t
    Show<override>():string = "box"
sizer(t:type) := interface:
    Size():int
impl(t:type) := class(sizer(t)):
    Size<override>():int = 1
more(t:type, u:type) := class(impl(t)):
    W:u
    Size<override>():int = 2
ShowAll(Ss:[]shower):[]string = for (S : Ss) { S.Show() }
SizeOf(S:sizer(t) where t:type):int = S.Size()
Main():void =
    R := ShowAll(array{box(int){V := 1}, box(string){V := "s"}})
    Print("{R.Length} {SizeOf(impl(int){})} {SizeOf(more(int, string){W := "w"})}")
