One()<computes>:int=1
Two()<computes>:int=2
Pick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two
holder:=class{var E:event(int)}
session_key:=class<unique><module_scoped_var_weak_map_key>{}
var Holders:weak_map(session_key,holder)=map{}
Cache:=module:
    var NestedHolders<public>:weak_map(session_key,holder)=map{}
Put(Key:session_key,H:holder)<transacts><decides>:void=set Holders[Key]=H
Get(Key:session_key)<transacts><decides>:holder=Holders[Key]
Change(Key:session_key,E:event(int))<transacts><decides>:void=
    Alias:=Get[Key]
    set Alias.E=E
Direct(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    if(set Holders[Key]=H,Alias:=Holders[Key]):
        set Alias.E=E
    H.E.Signal(0)
    Stored()
HelperGet(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    if(Put[Key,H],Alias:=Get[Key]):
        set Alias.E=E
    H.E.Signal(0)
    Stored()
HelperWrite(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    if(Put[Key,H],Change[Key,E]){}
    H.E.Signal(0)
    Stored()
SavedAlias(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    if(set Holders[Key]=H,Alias:=Holders[Key]):
        Saved:=Alias
        set Saved.E=E
    H.E.Signal(0)
    Stored()
Nested(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    if(set Cache.NestedHolders[Key]=H,Alias:=Cache.NestedHolders[Key]):
        set Alias.E=E
    H.E.Signal(0)
    Stored()
RollbackThenWrite(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    if(set Holders[Key]=H,Alias:=Holders[Key]):
        if(set Alias.E=Other;false?){}
        set Alias.E=E
    H.E.Signal(0)
    Stored()
Unrelated(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    if(set Holders[Key]=H,Alias:=Holders[Key]):
        set Alias.E=Other
    H.E.Signal(0)
    Stored()
Rollback(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    if(set Holders[Key]=H;Alias:=Holders[Key];set Alias.E=E;false?){}
    H.E.Signal(0)
    Stored()
UnrelatedHolder(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=Other}
    if(set Holders[Key]=K,Alias:=Holders[Key]):
        set Alias.E=E
    H.E.Signal(0)
    Stored()
UnrelatedMap(Key:session_key,E:event(int),F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<suspends>:int=
    var Stored:type{_()<computes>:int}=Dummy
    branch:
        E.Await()
        set Stored=Dummy
    set Stored=F
    Other:=event(int){}
    H:=holder{E:=Other}
    K:=holder{E:=Other}
    if(set Cache.NestedHolders[Key]=K,Alias:=Cache.NestedHolders[Key]):
        set Alias.E=E
    H.E.Signal(0)
    Stored()
Main()<suspends>:void=
    Print("Direct {Direct(session_key{},event(int){},One,Two)}")
    Print("HelperGet {HelperGet(session_key{},event(int){},One,Two)}")
    Print("HelperWrite {HelperWrite(session_key{},event(int){},One,Two)}")
    Print("SavedAlias {SavedAlias(session_key{},event(int){},One,Two)}")
    Print("Nested {Nested(session_key{},event(int){},One,Two)}")
    Print("RollbackThenWrite {RollbackThenWrite(session_key{},event(int){},One,Two)}")
    Print("Unrelated {Unrelated(session_key{},event(int){},One,Two)}")
    Print("Rollback {Rollback(session_key{},event(int){},One,Two)}")
    Print("UnrelatedHolder {UnrelatedHolder(session_key{},event(int){},One,Two)}")
    Print("UnrelatedMap {UnrelatedMap(session_key{},event(int){},One,Two)}")
