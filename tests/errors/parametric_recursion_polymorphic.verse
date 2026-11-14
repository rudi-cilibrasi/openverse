# expect: field 'Next' of my_type names my_type(?t), my_type at other type arguments than its own: a parametric type refers to itself only as my_type(t) (Book of Verse ch. 10, "Disallowed: Polymorphic Recursion")
my_type(t:type) := class:
    Value:t
    Next:?my_type(?t) = false
Main():void = Print("{my_type(int){Value := 1}.Value}")
