F(N:int)<computes>:int=
    if(N=0):return 0|1
    if(N=1):return 0|1
    if(N=2):return 0|1
    if(N=3):return 0|1
    if(N=4):return 0|1
    if(N=5):return 0|1
    if(N=6):return 0|1
    if(N=7):return 0|1
    if(N=8):return 0|1
    if(N=9):return 0|1
    if(N=10):return 0|1
    if(N=11):return 0|1
    if(N=12):return 0|1
    if(N=13):return 0|1
    if(N=14):return 0|1
    if(N=15):return 0|1
    if(N=16):return 0|1
    if(N=17):return 0|1
    if(N=18):return 0|1
    if(N=19):return 0|1
    if(N=20):return 0|1
    2|3
Main():void=
    for(N:array{-1,0,10,20,21}):
        for(V:=F(N)){Print("all {N} {V}")}
    if(V:=F(20),V=1)then Print("first {V}")else Print("bad")
    if(V:=F(0),V=2)then Print("bad fallthrough")else Print("no fallthrough")
    if(V:=F(0),V=9)then Print("bad reject")else Print("none")
    if(V:=option{F(0)}?)then Print("option {V}")else Print("bad option")
    for(V:=first{F(0)}){Print("first block {V}")}
