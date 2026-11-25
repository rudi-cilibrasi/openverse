# Control for book-join-common-base-interface:
# Tests/Bugs/SOL-5838-JoinOfClassesWithCommonBaseClassWithInterfaceInheritance.versetest:11
# accepts the array when the interfaces are the base class's.
super_interface_1 := interface{}
super_interface_2 := interface{}
super_class := class(super_interface_1, super_interface_2){}
sub_class_1 := class(super_class){}
sub_class_2 := class(super_class){}

F(X:[]super_class):void = {}

Main():void =
    F(array{sub_class_1{}, sub_class_2{}})
    Print("OVPROBE called")
