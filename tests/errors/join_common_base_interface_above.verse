# expect: the elements of this array (class2, class3) have more than one nearest common supertype (class1, interface2), so it is an array of any, not of interface1
# the same where an interface above both nearest supertypes is expected:
# the array's own type, of any, is refused (the Book of Verse's tests,
# SOL-5838-JoinOfClassesWithCommonBaseClassWithInterfaceInheritance.versetest:22)
interface1 := interface {}
class1 := class(interface1) {}
interface2 := interface(interface1) {}
class2 := class(class1, interface2) {}
class3 := class(class1, interface2) {}
F(X:[]interface1):void = {}
Main():void =
    F(array{class2{}, class3{}})
