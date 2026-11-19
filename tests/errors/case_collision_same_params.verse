# expect: have names that differ only in case and take the same parameters
# The same parameter types, return types apart (#724): UEFN 43.12 refuses
# two such functions with 9000 twice (followup-book2/case-collision-same-params;
# the Book's FORT-793952 :199 and, return types apart, :205).
Function(Value:int):int = Value
FUNCTION(Value:int):float = 42.0
Main():void = Print("{Function(1)}")
