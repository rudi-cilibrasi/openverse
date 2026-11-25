# Field values of reference/value classes, structs, inherited and aliased
# classes, and nested constructors all keep the cast's generic refinement.
pair(a:type,b:type):=class:
    A:a
    B:b
dup(t:type):=class(pair(t,t)){}
cbox(t:type):=class{Value:t}
vbox(t:type):=class<computes>{Value:t}
sbox(t:type):=struct{Value:t}
child(t:type):=class(cbox(t)){Flag:int=9}
alias(t:type):=cbox(t)
nested(t:type):=struct{Inner:cbox(t)}
gbox(t:type):=class{Before:?t=false;Value:t;After:[]t=array{}}
DirectClass(P:pair(a,b) where a:type,b:type)<transacts><decides>:cbox(b)=cbox(b){Value:=dup[P].A}
NamedClass(P:pair(a,b) where a:type,b:type)<transacts><decides>:cbox(b)=(D:=dup[P];cbox(b){Value:=D.A})
DirectValue(P:pair(a,b) where a:type,b:type)<transacts><decides>:vbox(b)=vbox(b){Value:=dup[P].A}
NamedValue(P:pair(a,b) where a:type,b:type)<transacts><decides>:vbox(b)=(D:=dup[P];vbox(b){Value:=D.A})
DirectStruct(P:pair(a,b) where a:type,b:type)<transacts><decides>:sbox(b)=sbox(b){Value:=dup[P].A}
NamedStruct(P:pair(a,b) where a:type,b:type)<transacts><decides>:sbox(b)=(D:=dup[P];sbox(b){Value:=D.A})
DirectChild(P:pair(a,b) where a:type,b:type)<transacts><decides>:child(b)=child(b){Value:=dup[P].A}
NamedChild(P:pair(a,b) where a:type,b:type)<transacts><decides>:child(b)=(D:=dup[P];child(b){Value:=D.A})
DirectAlias(P:pair(a,b) where a:type,b:type)<transacts><decides>:alias(b)=alias(b){Value:=dup[P].A}
NamedAlias(P:pair(a,b) where a:type,b:type)<transacts><decides>:alias(b)=(D:=dup[P];alias(b){Value:=D.A})
DirectNested(P:pair(a,b) where a:type,b:type)<transacts><decides>:nested(b)=nested(b){Inner:=cbox(b){Value:=dup[P].A}}
NamedNested(P:pair(a,b) where a:type,b:type)<transacts><decides>:nested(b)=(D:=dup[P];nested(b){Inner:=cbox(b){Value:=D.A}})
DirectDefaults(P:pair(a,b) where a:type,b:type)<transacts><decides>:gbox(b)=gbox(b){Value:=dup[P].A}
NamedDefaults(P:pair(a,b) where a:type,b:type)<transacts><decides>:gbox(b)=(D:=dup[P];gbox(b){Value:=D.A})
Rest(P:pair(a,b) where a:type,b:type)<transacts><decides>:b=(X:=cbox(b){Value:=dup[P].A};P.A)
RestNamed(P:pair(a,b) where a:type,b:type)<transacts><decides>:b=(D:=dup[P];X:=cbox(b){Value:=D.A};P.A)
Main():void=
    if(V:=DirectClass[dup(int){A:=7,B:=9}],W:=NamedClass[dup(int){A:=7,B:=9}]) then Print("class int {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectClass[dup(string){A:="left",B:="right"}],W:=NamedClass[dup(string){A:="left",B:="right"}]) then Print("class string {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectValue[dup(int){A:=7,B:=9}],W:=NamedValue[dup(int){A:=7,B:=9}]) then Print("value int {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectValue[dup(string){A:="left",B:="right"}],W:=NamedValue[dup(string){A:="left",B:="right"}]) then Print("value string {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectStruct[dup(int){A:=7,B:=9}],W:=NamedStruct[dup(int){A:=7,B:=9}]) then Print("struct int {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectStruct[dup(string){A:="left",B:="right"}],W:=NamedStruct[dup(string){A:="left",B:="right"}]) then Print("struct string {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectChild[dup(int){A:=7,B:=9}],W:=NamedChild[dup(int){A:=7,B:=9}]) then Print("child int {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectChild[dup(string){A:="left",B:="right"}],W:=NamedChild[dup(string){A:="left",B:="right"}]) then Print("child string {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectAlias[dup(int){A:=7,B:=9}],W:=NamedAlias[dup(int){A:=7,B:=9}]) then Print("alias int {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectAlias[dup(string){A:="left",B:="right"}],W:=NamedAlias[dup(string){A:="left",B:="right"}]) then Print("alias string {V.Value} {W.Value}") else Print("wrong")
    if(V:=DirectNested[dup(int){A:=7,B:=9}],W:=NamedNested[dup(int){A:=7,B:=9}]) then Print("nested int {V.Inner.Value} {W.Inner.Value}") else Print("wrong")
    if(V:=DirectNested[dup(string){A:="left",B:="right"}],W:=NamedNested[dup(string){A:="left",B:="right"}]) then Print("nested string {V.Inner.Value} {W.Inner.Value}") else Print("wrong")
    if(V:=DirectDefaults[dup(int){A:=7,B:=9}],W:=NamedDefaults[dup(int){A:=7,B:=9}]) then Print("defaults int {V.Value} {W.Value} {V.After.Length} {W.After.Length}") else Print("wrong")
    if(V:=DirectDefaults[dup(string){A:="left",B:="right"}],W:=NamedDefaults[dup(string){A:="left",B:="right"}]) then Print("defaults string {V.Value} {W.Value} {V.After.Length} {W.After.Length}") else Print("wrong")
    if(V:=Rest[dup(int){A:=7,B:=9}],W:=RestNamed[dup(int){A:=7,B:=9}]) then Print("rest {V} {W}") else Print("wrong")
