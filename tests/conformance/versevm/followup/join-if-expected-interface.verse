named := interface{}
pet := class{}
cat := class(pet, named){}
bird := class(pet, named){}

Pick(B:logic):named =
    if (B?) then cat{} else bird{}

Main():void =
    X := Pick(true)
    Print("OVPROBE picked")
