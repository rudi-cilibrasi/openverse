F(Items:[][string]t,Fallback:t where t:type)<transacts>:t=
    for(Outer -> Original:Items):
        var Current:[string]t=Original
        for(Key -> Item:Current):
            Print("row {Outer} {Key}")
            set Current=map{"replacement"=>Fallback}
            if(Outer=1,Key="a"):return Item|(Current["replacement"] or Fallback)
    Fallback|Fallback
Main()<transacts>:void=
    Input:=array{map{"z"=>1,"a"=>2},map{"b"=>3,"a"=>4}}
    for(V:=F(Input,99)):Print("all {V}")
    if(V:=F(Input,99),V=99)then Print("first {V}")else Print("bad")
    if(V:=F(Input,99),V=999)then Print("bad")else Print("none")
    for(V:=F(array{map{"a"=>2}},7)):Print("short {V}")
    for(V:=F(array{map{"z"=>"skip"},map{"a"=>"b"}},"x")):Print("string {V}")
