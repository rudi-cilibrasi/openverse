# void given as a type argument is true, the empty value's type alone (Book
# of Verse ch. 2, "Write the value, not the type name": void that reaches a
# parameter through a type parameter takes the empty value only): the empty
# value, a void value, []true and ?true fit; a parameter written :void, and
# []void written, still take any value.
class1(t:type) := class:
    Foo(:t):string = "foo"
    Keep(X:t):t = X
holder(t:type) := interface:
    Method(X:t):t = X
holder_void := holder(void)
c := class(holder_void) {}
Sink(:[]void):string = "sink"
Main():void =
    X:void = 1
    T:[]true = array{false, ()}
    O:?true = option{false}
    Print("{class1(void){}.Foo(false)} {class1(void){}.Foo()} {class1(void){}.Foo(X)}")
    Print("{class1([]void){}.Foo(T)} {class1(?void){}.Foo(O)} {class1([]void){}.Keep(T).Length}")
    C := c{}
    if (C.Method(false) = ()) then Print("empty")
    Y:[]int = array{1, 2}
    Print(Sink(Y))
