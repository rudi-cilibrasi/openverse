# More than eight distinct witness-discovery steps through default spawns.
holder(t:type) := class { Marker:t }
i0(v0:type) := interface { Go0(?N:int=0)<suspends>:void }
a0(u:type) := class(holder(u),i0(u)):
    Seed:int=0
    Go0<override>(?N:int=block{Q:i1(u)=a1(u){Marker:=Marker};T:=spawn{Q.Go1()};Seed})<suspends>:void=Print("body 0 {N}")
i1(v1:type) := interface { Go1(?N:int=0)<suspends>:void }
a1(u:type) := class(holder(u),i1(u)):
    Seed:int=1
    Go1<override>(?N:int=block{Q:i2(u)=a2(u){Marker:=Marker};T:=spawn{Q.Go2()};Seed})<suspends>:void=Print("body 1 {N}")
i2(v2:type) := interface { Go2(?N:int=0)<suspends>:void }
a2(u:type) := class(holder(u),i2(u)):
    Seed:int=2
    Go2<override>(?N:int=block{Q:i3(u)=a3(u){Marker:=Marker};T:=spawn{Q.Go3()};Seed})<suspends>:void=Print("body 2 {N}")
i3(v3:type) := interface { Go3(?N:int=0)<suspends>:void }
a3(u:type) := class(holder(u),i3(u)):
    Seed:int=3
    Go3<override>(?N:int=block{Q:i4(u)=a4(u){Marker:=Marker};T:=spawn{Q.Go4()};Seed})<suspends>:void=Print("body 3 {N}")
i4(v4:type) := interface { Go4(?N:int=0)<suspends>:void }
a4(u:type) := class(holder(u),i4(u)):
    Seed:int=4
    Go4<override>(?N:int=block{Q:i5(u)=a5(u){Marker:=Marker};T:=spawn{Q.Go5()};Seed})<suspends>:void=Print("body 4 {N}")
i5(v5:type) := interface { Go5(?N:int=0)<suspends>:void }
a5(u:type) := class(holder(u),i5(u)):
    Seed:int=5
    Go5<override>(?N:int=block{Q:i6(u)=a6(u){Marker:=Marker};T:=spawn{Q.Go6()};Seed})<suspends>:void=Print("body 5 {N}")
i6(v6:type) := interface { Go6(?N:int=0)<suspends>:void }
a6(u:type) := class(holder(u),i6(u)):
    Seed:int=6
    Go6<override>(?N:int=block{Q:i7(u)=a7(u){Marker:=Marker};T:=spawn{Q.Go7()};Seed})<suspends>:void=Print("body 6 {N}")
i7(v7:type) := interface { Go7(?N:int=0)<suspends>:void }
a7(u:type) := class(holder(u),i7(u)):
    Seed:int=7
    Go7<override>(?N:int=block{Q:i8(u)=a8(u){Marker:=Marker};T:=spawn{Q.Go8()};Seed})<suspends>:void=Print("body 7 {N}")
i8(v8:type) := interface { Go8(?N:int=0)<suspends>:void }
a8(u:type) := class(holder(u),i8(u)):
    Seed:int=8
    Go8<override>(?N:int=block{Q:i9(u)=a9(u){Marker:=Marker};T:=spawn{Q.Go9()};Seed})<suspends>:void=Print("body 8 {N}")
i9(v9:type) := interface { Go9(?N:int=0)<suspends>:void }
a9(u:type) := class(holder(u),i9(u)):
    Seed:int=9
    Go9<override>(?N:int=Seed)<suspends>:void=Print("body 9 {N}")
Start(P:i0(t) where t:type):task(void)=spawn{P.Go0()}
Main():void=
    T:=Start(a0(string){Marker:="x"})
    Print("created")
