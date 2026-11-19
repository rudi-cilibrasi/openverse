# Second control of parametric-interface-var: a var field in an interface
# that is not parametric (the Book's ch. 10 has interface fields). Not a
# Book case. OpenVerse prints
#   defined
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# 2026-11-19) admits it, and its Verse VM prints defined, as OpenVerse does.
j<public> := interface:
    var Data<public>:int

Main():void =
    Print("OVPROBE defined")
