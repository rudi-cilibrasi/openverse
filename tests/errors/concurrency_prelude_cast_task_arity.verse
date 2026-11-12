# expect: a cast task[X] takes one value
Main():void=
    if(T:=task[]) then Print("bad")
