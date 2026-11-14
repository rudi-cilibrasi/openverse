# expect: F calls $GetCastableFinalSuperClass:base, which has the effect <reads>, which its effects (<computes>) do not allow
# the API reference declares both functions <reads><decides>
base := class<castable> {}
anchor := class<final_super>(base) {}
F(X:base)<computes>:logic = if (GetCastableFinalSuperClass[base, X]) then true else false
Main():void = Print("ok")
