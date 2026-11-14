# expect: GetCastableFinalSuperClass's first argument is a type written there, the base type, and B is no type openverse knows there
base := class<castable> {}
anchor := class<final_super>(base) {}
Main():void =
    B := base{}
    if (GetCastableFinalSuperClass[B, anchor{}]) then Print("found")
