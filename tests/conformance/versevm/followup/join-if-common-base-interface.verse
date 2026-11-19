super_interface := interface{}
super_class := class{}
sub_class_1 := class(super_class, super_interface){}
sub_class_2 := class(super_class, super_interface){}

Pick(B:logic):super_class =
    if (B?) then sub_class_1{} else sub_class_2{}

Main():void =
    X := Pick(true)
    Print("OVPROBE picked")
