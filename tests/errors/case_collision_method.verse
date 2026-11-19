# expect: have names that differ only in case and take the same parameters
# Two methods of one class, names differing only in case (#724): UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses them with error 9200
# (followup-book2/case-collision-method; the Book's FORT-793952 :5).
cc := class:
    Function():int = 42
    FUNCTION():int = 420
Main():void = Print("{cc{}.Function()}")
