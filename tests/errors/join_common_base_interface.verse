# expect: 13:13: the elements of this array (sub_class_1, sub_class_2) have more than one nearest common supertype (super_class, super_interface), so it is an array of any, not of super_class (Epic's Verse compiler, UEFN 43.12: error 3509)
# two classes with a common base class and a common interface not above it
# have two nearest common supertypes: an array of both is an array of any.
# UEFN 43.12 (++Fortnite+Release-43.12-CL-60598086) refuses it where an
# array of the base class is expected, error 3509 (the Book of Verse's
# tests, SOL-5838-JoinOfClassesWithCommonBaseClassWithInterfaceInheritance.versetest:13;
# tests/conformance/versevm/book/book-join-common-base-interface.verse)
super_interface := interface{}
super_class := class{}
sub_class_1 := class(super_class, super_interface){}
sub_class_2 := class(super_class, super_interface){}
F(X:[]super_class):void = {}
G():void = F(array{sub_class_1{}, sub_class_2{}})
Main():void =
    G()
