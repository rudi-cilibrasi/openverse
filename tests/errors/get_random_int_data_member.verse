# expect: might not complete
# GetRandomInt is <transacts>, not <converges>: no data member's definition
# calls it (UEFN 43.12: error 3582; #724).
Seed:int = GetRandomInt(1, 6)
Main():void = Print("{Seed}")
