# expect: Function and FUNCTION, of ii, have names that differ only in case and take the same parameters
# An interface's two methods whose names differ only in case (#724): UEFN
# 43.12 (++Fortnite+Release-43.12-CL-60598086) refuses them, error 9200
# (followup-book3/case-collision-interface).
ii := interface:
    Function():int = 42
    FUNCTION():int = 420
impl := class(ii) {}
Main():void = Print("{impl{}.Function()}")
