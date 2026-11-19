# Map domains survive lifting through each known call-argument shape.
Empty(?Default:?t=false where t:type)<transacts>:?t=Default
Id(X:t where t:type)<transacts>:t=X
pair(a:type,b:type):=class{A:a;B:b}
dup(t:type):=class(pair(t,t)){Index:int=0}
Leaf(X:t,?Index:int=0 where t:type)<transacts>:t=X
Choose(M:[?int]t,Other:t where t:type)<transacts>:t=Other
NamedMap(Other:t,?Values:[?int]t where t:type)<transacts>:t=Other
NamedOther(M:[?int]t,?Other:t where t:type)<transacts>:t=Other
Array(M:[][?int]t,Other:t where t:type)<transacts>:t=Other
Option(M:?[?int]t,Other:t where t:type)<transacts>:t=Other
Tuple(M:tuple([?int]t,int),Other:t where t:type)<transacts>:t=Other
Nested(M:[?int][?string]t,Other:t where t:type)<transacts>:t=Other
Weak(M:weak_map(?int,t),Other:t where t:type)<transacts>:t=Other
Key(V:?int)<transacts>:?int=V
Case_map(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Choose(map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)},dup[P].B)
Case_wrapped_key(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Choose(map{Id(Empty())=>Leaf(P.A,?Index:=dup[Q].Index)},dup[P].B)
Case_named_map(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    NamedMap(dup[P].B,?Values:=map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)})
Case_named_other(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    NamedOther(map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)},?Other:=dup[P].B)
Case_array_map(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Array(array{map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)}},dup[P].B)
Case_option_map(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Option(option{map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)}},dup[P].B)
Case_tuple_map(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Tuple((map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)},0),dup[P].B)
Case_nested_map(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Nested(map{Empty()=>map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)}},dup[P].B)
Case_weak_map(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Weak(map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)},dup[P].B)
Case_nested_call(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Choose(map{Empty()=>Choose(map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index)},dup[P].B)},dup[P].B)
Case_multiple_keys(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Choose(map{Empty()=>Leaf(P.A,?Index:=dup[Q].Index),Empty(?Default:=option{0})=>P.A},dup[P].B)
Case_explicit_key_control(P:pair(a,b),Q:pair(c,d) where a:type,b:type,c:type,d:type)<transacts><decides>:b=
    Choose(map{Key(Empty())=>Leaf(P.A,?Index:=dup[Q].Index)},dup[P].B)
Main():void=
    if(V:=Case_map[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("map value {V}")else Print("map wrong")
    if(V:=Case_map[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("map wrong")else Print("map missing")
    if(V:=Case_map[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("map wrong")else Print("map other missing")
    if(V:=Case_wrapped_key[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("wrapped_key value {V}")else Print("wrapped_key wrong")
    if(V:=Case_wrapped_key[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("wrapped_key wrong")else Print("wrapped_key missing")
    if(V:=Case_wrapped_key[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("wrapped_key wrong")else Print("wrapped_key other missing")
    if(V:=Case_named_map[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("named_map value {V}")else Print("named_map wrong")
    if(V:=Case_named_map[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("named_map wrong")else Print("named_map missing")
    if(V:=Case_named_map[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("named_map wrong")else Print("named_map other missing")
    if(V:=Case_named_other[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("named_other value {V}")else Print("named_other wrong")
    if(V:=Case_named_other[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("named_other wrong")else Print("named_other missing")
    if(V:=Case_named_other[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("named_other wrong")else Print("named_other other missing")
    if(V:=Case_array_map[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("array_map value {V}")else Print("array_map wrong")
    if(V:=Case_array_map[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("array_map wrong")else Print("array_map missing")
    if(V:=Case_array_map[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("array_map wrong")else Print("array_map other missing")
    if(V:=Case_option_map[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("option_map value {V}")else Print("option_map wrong")
    if(V:=Case_option_map[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("option_map wrong")else Print("option_map missing")
    if(V:=Case_option_map[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("option_map option empty {V}")else Print("option_map wrong")
    if(V:=Case_tuple_map[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("tuple_map value {V}")else Print("tuple_map wrong")
    if(V:=Case_tuple_map[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("tuple_map wrong")else Print("tuple_map missing")
    if(V:=Case_tuple_map[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("tuple_map wrong")else Print("tuple_map other missing")
    if(V:=Case_nested_map[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("nested_map value {V}")else Print("nested_map wrong")
    if(V:=Case_nested_map[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("nested_map wrong")else Print("nested_map missing")
    if(V:=Case_nested_map[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("nested_map wrong")else Print("nested_map other missing")
    if(V:=Case_weak_map[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("weak_map value {V}")else Print("weak_map wrong")
    if(V:=Case_weak_map[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("weak_map wrong")else Print("weak_map missing")
    if(V:=Case_weak_map[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("weak_map wrong")else Print("weak_map other missing")
    if(V:=Case_nested_call[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("nested_call value {V}")else Print("nested_call wrong")
    if(V:=Case_nested_call[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("nested_call wrong")else Print("nested_call missing")
    if(V:=Case_nested_call[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("nested_call wrong")else Print("nested_call other missing")
    if(V:=Case_multiple_keys[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("multiple_keys value {V}")else Print("multiple_keys wrong")
    if(V:=Case_multiple_keys[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("multiple_keys wrong")else Print("multiple_keys missing")
    if(V:=Case_multiple_keys[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("multiple_keys wrong")else Print("multiple_keys other missing")
    if(V:=Case_explicit_key_control[dup(int){A:=7,B:=9},dup(string){A:="left",B:="right"}])then Print("explicit_key_control value {V}")else Print("explicit_key_control wrong")
    if(V:=Case_explicit_key_control[pair(int,string){A:=7,B:="bad"},dup(string){A:="left",B:="right"}])then Print("explicit_key_control wrong")else Print("explicit_key_control missing")
    if(V:=Case_explicit_key_control[dup(int){A:=7,B:=9},pair(int,string){A:=1,B:="bad"}])then Print("explicit_key_control wrong")else Print("explicit_key_control other missing")
