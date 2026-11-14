# expect: 8:15: default of field 'V' of c requires convergence: ordinary function 'GetCastableFinalSuperClass' has no checked convergence contract
# A message names the built-in a program calls, not the helper openverse
# writes for the call.
base := class<castable>:
    Id:int = 0
anchor := class<final_super>(base) {}
c := class:
    V:string = if (T := GetCastableFinalSuperClass[base, anchor{}]) then "y" else "n"
Main():void = Print(c{}.V)
