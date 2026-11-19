# expect: using a value of type type{_():int} as a value of type type{_():rational} is not yet implemented: this branch of an if
# (#724) the branches of an if return an int and a rational, at
# type{_():rational}: int to rational changes the value, a wrapper Epic's
# Verse compiler does not make for a branch (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502, "Using a
# value of type tuple()->int as a value of type tuple()->rational":
# followup-coerce2/join-int-rational). Named alone at the type, a function of
# an int is admitted (followup-coerce2/name-int-rational-param).
Three():int = 3
Third():rational = 3
Pick(Flag:logic):int =
    F:type{_():rational} = if (Flag?) { Three } else { Third }
    Floor(F())
Main():void =
    Print("{Pick(true)}")
