# Book: Tests/Bugs/SOL-5838-JoinOfClassesWithCommonBaseClassWithInterfaceInheritance.versetest:13
# refuses (3509) an array of two classes that share a base class and an
# interface, passed where an array of the base class is expected.
super_interface := interface{}
super_class := class{}
sub_class_1 := class(super_class, super_interface){}
sub_class_2 := class(super_class, super_interface){}

F(X:[]super_class):void = {}
G():void = F(array{sub_class_1{}, sub_class_2{}})

Main():void =
    G()
    Print("OVPROBE called")
