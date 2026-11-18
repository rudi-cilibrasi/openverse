# arrays of classes with one nearest common supertype keep it (UEFN 43.12
# admits tests/conformance/versevm/book/book-join-common-base-interface-control.verse,
# the Book of Verse's SOL-5838...versetest:11), and an array of classes
# with two is one of any where nothing else, or any, is expected
super_interface_1 := interface{}
super_interface_2 := interface{}
super_class := class(super_interface_1, super_interface_2){}
sub_class_1 := class(super_class){}
sub_class_2 := class(super_class){}
F(X:[]super_class):void = Print("bases {X.Length}")
shared := interface{}
base := class{}
left := class(base, shared){}
right := class(base, shared){}
Count(X:[]any):int = X.Length
Main():void =
    F(array{sub_class_1{}, sub_class_2{}})
    Mixed := array{left{}, right{}}
    Print("mixed {Count(Mixed)}")
    Print("any {Count(array{left{}, right{}, base{}})}")
