Pick(Items:[]t,Default:t where t:type)<computes>:t=
    for(I:Items):return I
    Default|Default
Main():void=
    for(V:=Pick(array{7,8},9)){Print("i {V}")}
    for(V:=Pick(array{},9)){Print("e {V}")}
    for(V:=Pick(array{"a","b"},"z")){Print("s {V}")}
