# expect: unknown identifier 'Later'
Values(N:int)<transacts>:int =
    if(N<0):return 0
    defer:Print("{Later}")
    Later:=N|N+1
    Later
Main():void=for(V:=Values(1)):Print("{V}")
