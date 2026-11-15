One()<computes>:int=1
Two()<computes>:int=2
Pick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two
session_key:=class<unique><module_scoped_var_weak_map_key>{}
function_box:=class{Value:type{_()<computes>:int}}
var Functions:weak_map(session_key,type{_()<computes>:int})=map{}
var Optional:weak_map(session_key,?type{_()<computes>:int})=map{}
var Boxes:weak_map(session_key,function_box)=map{}
Cache:=module:
    var NestedFunctions<public>:weak_map(session_key,type{_()<computes>:int})=map{}
Identity(V:v where v:type)<computes>:v=V
Ignore(V:v,Real:type{_()<computes>:int} where v:type)<computes>:type{_()<computes>:int}=Real
Put(Key:session_key,Value:type{_()<computes>:int})<transacts><decides>:void=set Functions[Key]=Value
Get(Key:session_key)<transacts><decides>:type{_()<computes>:int}=Functions[Key]
StorageDirect(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Functions[Key]=Dummy,V:=Functions[Key])then V()else 0
StorageUnused(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Functions[Key]=Dummy){}
    0
StorageHelper(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(Put[Key,Dummy],V:=Get[Key])then V()else 0
StorageGeneric(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Functions[Key]=Identity(Dummy),V:=Functions[Key])then V()else 0
StorageOptional(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Optional[Key]=option{Dummy},Maybe:=Optional[Key],V:=Maybe?)then V()else 0
StorageBoxed(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    H:=function_box{Value:=Dummy}
    if(set Boxes[Key]=H,V:=Boxes[Key])then V.Value()else 0
StorageNested(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Cache.NestedFunctions[Key]=Dummy,V:=Cache.NestedFunctions[Key])then V()else 0
StorageRollback(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Functions[Key]=Dummy;false?){}
    0
StorageOverwrite(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Functions[Key]=Dummy;set Functions[Key]=F;V:=Functions[Key])then V()else 0
StorageReal(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Functions[Key]=F,V:=Functions[Key])then V()else 0
StorageIgnoreMetadata(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Functions[Key]=Ignore(Dummy,F),V:=Functions[Key])then V()else 0
StorageRealHelper(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(Put[Key,Ignore(Dummy,F)],V:=Get[Key])then V()else 0
StorageRealRollback(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Functions[Key]=F){}
    if(set Functions[Key]=Ignore(Dummy,F);false?){}
    if(V:=Functions[Key])then V()else 0
StorageRealOptional(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    if(set Optional[Key]=option{Ignore(Dummy,F)},Maybe:=Optional[Key],V:=Maybe?)then V()else 0
StorageRealBoxed(Key:session_key,F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<transacts>:int=
    H:=function_box{Value:=Ignore(Dummy,F)}
    if(set Boxes[Key]=H,V:=Boxes[Key])then V.Value()else 0
Main():void=
    Print("Direct {StorageDirect(session_key{},One,Two)}")
    Print("Unused {StorageUnused(session_key{},One,Two)}")
    Print("Helper {StorageHelper(session_key{},One,Two)}")
    Print("Generic {StorageGeneric(session_key{},One,Two)}")
    Print("Optional {StorageOptional(session_key{},One,Two)}")
    Print("Boxed {StorageBoxed(session_key{},One,Two)}")
    Print("Nested {StorageNested(session_key{},One,Two)}")
    Print("Rollback {StorageRollback(session_key{},One,Two)}")
    Print("Overwrite {StorageOverwrite(session_key{},One,Two)}")
    Print("Real {StorageReal(session_key{},One,Two)}")
    Print("IgnoreMetadata {StorageIgnoreMetadata(session_key{},One,Two)}")
    Print("RealHelper {StorageRealHelper(session_key{},One,Two)}")
    Print("RealRollback {StorageRealRollback(session_key{},One,Two)}")
    Print("RealOptional {StorageRealOptional(session_key{},One,Two)}")
    Print("RealBoxed {StorageRealBoxed(session_key{},One,Two)}")
