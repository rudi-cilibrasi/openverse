# Generic argument probes must preserve errors that trigger cast lifting.
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Index:int=9}
Id(X:t where t:type)<transacts>:t=X
Run_plain_2(P:pair(a,b) where a:type,b:type)<transacts><decides>:b=
    X:=Id(Id(dup[P].B))
    X
Run_block_2(P:pair(a,b) where a:type,b:type)<transacts><decides>:int=
    X:=Id(block{Id(Id(dup[P].Index))})
    X
Run_option_2(P:pair(a,b) where a:type,b:type)<transacts><decides>:?int=
    X:=Id(option{Id(Id(dup[P].Index))})
    X
Run_option_block_2(P:pair(a,b) where a:type,b:type)<transacts><decides>:?int=
    X:=Id(option{block{Id(Id(dup[P].Index))}})
    X
Run_array_2(P:pair(a,b) where a:type,b:type)<transacts><decides>:[]b=
    X:=Id(array{Id(Id(dup[P].B))})
    X
Run_map_2(P:pair(a,b) where a:type,b:type)<transacts><decides>:[int]b=
    X:=Id(map{0=>Id(Id(dup[P].B))})
    X
Run_plain_4(P:pair(a,b) where a:type,b:type)<transacts><decides>:b=
    X:=Id(Id(Id(Id(dup[P].B))))
    X
Run_block_4(P:pair(a,b) where a:type,b:type)<transacts><decides>:int=
    X:=Id(block{Id(Id(Id(Id(dup[P].Index))))})
    X
Run_option_4(P:pair(a,b) where a:type,b:type)<transacts><decides>:?int=
    X:=Id(option{Id(Id(Id(Id(dup[P].Index))))})
    X
Run_option_block_4(P:pair(a,b) where a:type,b:type)<transacts><decides>:?int=
    X:=Id(option{block{Id(Id(Id(Id(dup[P].Index))))}})
    X
Run_array_4(P:pair(a,b) where a:type,b:type)<transacts><decides>:[]b=
    X:=Id(array{Id(Id(Id(Id(dup[P].B))))})
    X
Run_map_4(P:pair(a,b) where a:type,b:type)<transacts><decides>:[int]b=
    X:=Id(map{0=>Id(Id(Id(Id(dup[P].B))))})
    X
Main():void=
    if(V:=Run_plain_2[dup(int){A:=7,B:=9}],N:=V)then Print("plain-2 value {N}")else Print("plain-2 none")
    if(V:=Run_plain_2[pair(int,string){A:=7,B:="bad"}],N:=V)then Print("plain-2 wrong")else Print("plain-2 none")
    if(V:=Run_block_2[dup(int){A:=7,B:=9}],N:=V)then Print("block-2 value {N}")else Print("block-2 none")
    if(V:=Run_block_2[pair(int,string){A:=7,B:="bad"}],N:=V)then Print("block-2 wrong")else Print("block-2 none")
    if(V:=Run_option_2[dup(int){A:=7,B:=9}],N:=V?)then Print("option-2 value {N}")else Print("option-2 none")
    if(V:=Run_option_2[pair(int,string){A:=7,B:="bad"}],N:=V?)then Print("option-2 wrong")else Print("option-2 none")
    if(V:=Run_option_block_2[dup(int){A:=7,B:=9}],N:=V?)then Print("option_block-2 value {N}")else Print("option_block-2 none")
    if(V:=Run_option_block_2[pair(int,string){A:=7,B:="bad"}],N:=V?)then Print("option_block-2 wrong")else Print("option_block-2 none")
    if(V:=Run_array_2[dup(int){A:=7,B:=9}],N:=V[0])then Print("array-2 value {N}")else Print("array-2 none")
    if(V:=Run_array_2[pair(int,string){A:=7,B:="bad"}],N:=V[0])then Print("array-2 wrong")else Print("array-2 none")
    if(V:=Run_map_2[dup(int){A:=7,B:=9}],N:=V[0])then Print("map-2 value {N}")else Print("map-2 none")
    if(V:=Run_map_2[pair(int,string){A:=7,B:="bad"}],N:=V[0])then Print("map-2 wrong")else Print("map-2 none")
    if(V:=Run_plain_4[dup(int){A:=7,B:=9}],N:=V)then Print("plain-4 value {N}")else Print("plain-4 none")
    if(V:=Run_plain_4[pair(int,string){A:=7,B:="bad"}],N:=V)then Print("plain-4 wrong")else Print("plain-4 none")
    if(V:=Run_block_4[dup(int){A:=7,B:=9}],N:=V)then Print("block-4 value {N}")else Print("block-4 none")
    if(V:=Run_block_4[pair(int,string){A:=7,B:="bad"}],N:=V)then Print("block-4 wrong")else Print("block-4 none")
    if(V:=Run_option_4[dup(int){A:=7,B:=9}],N:=V?)then Print("option-4 value {N}")else Print("option-4 none")
    if(V:=Run_option_4[pair(int,string){A:=7,B:="bad"}],N:=V?)then Print("option-4 wrong")else Print("option-4 none")
    if(V:=Run_option_block_4[dup(int){A:=7,B:=9}],N:=V?)then Print("option_block-4 value {N}")else Print("option_block-4 none")
    if(V:=Run_option_block_4[pair(int,string){A:=7,B:="bad"}],N:=V?)then Print("option_block-4 wrong")else Print("option_block-4 none")
    if(V:=Run_array_4[dup(int){A:=7,B:=9}],N:=V[0])then Print("array-4 value {N}")else Print("array-4 none")
    if(V:=Run_array_4[pair(int,string){A:=7,B:="bad"}],N:=V[0])then Print("array-4 wrong")else Print("array-4 none")
    if(V:=Run_map_4[dup(int){A:=7,B:=9}],N:=V[0])then Print("map-4 value {N}")else Print("map-4 none")
    if(V:=Run_map_4[pair(int,string){A:=7,B:="bad"}],N:=V[0])then Print("map-4 wrong")else Print("map-4 none")
