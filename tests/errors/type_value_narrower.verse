# expect: expected subtype(sub_class), found subtype(super_class)
super_class := class{}
sub_class := class(super_class) {}
F():void =
    L0:subtype(super_class) = super_class
    L1:subtype(sub_class) = L0
Main():void = {}
