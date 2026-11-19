# expect: interface i has type parameters and a var field, Data
# A parametric interface has no var field (#724): UEFN 43.12
# (++Fortnite+Release-43.12-CL-60598086) refuses one with error 3502,
# "Mutable members in parametric interfaces are not yet implemented"
# (followup-book2/parametric-interface-var; the Book's tests,
# ParametricFunctions.versetest:496).
i<public>(t:type) := interface:
    var Data<public>:t
Main():void = Print("defined")
