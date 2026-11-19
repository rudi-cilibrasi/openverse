# Second control of parametric-interface-var: a var field in an interface
# that is not parametric (the Book's ch. 10 has interface fields). Not a
# Book case. OpenVerse prints
#   defined
j<public> := interface:
    var Data<public>:int

Main():void =
    Print("OVPROBE defined")
