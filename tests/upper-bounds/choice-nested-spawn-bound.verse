vehicle:=class<allocates>:
    var N:int=10
    ReadN()<reads>:int=N
car:=class<allocates>(vehicle){Name:string="precise"}
Two(N:int):int=N|N+1
Shouter(X:t,N:int where t:subtype(vehicle))<suspends>:void=
    Sleep(0.0)
    Print("shout {X.ReadN()+N}")
Kick(X:t where t:subtype(vehicle)):t=
    R:=for(A0:=(Two(0)|Two(2)),A1:=(Two(0)|Two(2)),A2:=(Two(0)|Two(2)),A0=0,A1=0):
        spawn{Shouter(X,A2)}
        A2
    Print("values {R.Length}")
    X
Main()<suspends>:void=
    C:=car{}
    R:=Kick(C)
    set C.N=20
    Print("precise {R.Name} {R.N}")
    Sleep(0.1)
    Print("done")
