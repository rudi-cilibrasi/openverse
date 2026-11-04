# Rollback spans calls: output written by a failed callee is undone.
Check(X:int)<decides>:int =
    Print("checking {X}")
    X > 10

Main():void =
    if (Check[5]) then Print("big") else Print("small (the 'checking 5' line was rolled back)")
    if (Y := Check[50]) { Print("big {Y}") }
