F(N:int)<computes>:int=
    if(N=0):return 0|1
    if(N=1):return 10|11
    if(N=2):return 20|21
    if(N=3):return 30|31
    if(N=4):return 40|41
    if(N=5):return 50|51
    if(N=6):return 60|61
    if(N=7):return 70|71
    if(N=8):return 80|81
    if(N=9):return 90|91
    if(N=10):return 100|101
    if(N=11):return 110|111
    if(N=12):return 120|121
    if(N=13):return 130|131
    if(N=14):return 140|141
    if(N=15):return 150|151
    if(N=16):return 160|161
    if(N=17):return 170|171
    if(N=18):return 180|181
    if(N=19):return 190|191
    if(N=20):return 200|201
    2|3
Main():void=
    for(N:array{-1,0,10,20,21}):
        for(V:=F(N)){Print("all {N} {V}")}
    if(V:=F(20),V=201)then Print("first {V}")else Print("bad")
    if(V:=F(0),V=2)then Print("bad fallthrough")else Print("no fallthrough")
    if(V:=F(0),V=9)then Print("bad reject")else Print("none")
    if(V:=option{F(0)}?)then Print("option {V}")else Print("bad option")
    for(V:=first{F(0)}){Print("first block {V}")}
