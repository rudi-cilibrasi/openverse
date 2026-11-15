One()<computes>:int=1
Two()<computes>:int=2
Pick(C:logic)<computes>:type{_()<computes>:int}=if(C?)then One else Two
UseFn(Value:type{_()<computes>:int})<computes>:int=Value()
UseNamed(?Value:type{_()<computes>:int}=One)<computes>:int=Value()
box(v:type):=class<computes>{Value:v}
DirectMetadataPass(M:v,R:v where v:type)<computes>:v=M
ArgumentDirectMetadata(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    UseFn(DirectMetadataPass(Dummy,F))
DirectRealPass(M:v,R:v where v:type)<computes>:v=R
ArgumentDirectReal(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    UseFn(DirectRealPass(Dummy,F))
FailableMetadataPass(M:v,R:v where v:type)<decides><computes>:v=block{true?;M}
ArgumentFailableMetadata(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    if(V:=FailableMetadataPass[Dummy,F])then UseFn(V)else 0
FailableRealPass(M:v,R:v where v:type)<decides><computes>:v=block{true?;R}
ArgumentFailableReal(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    if(V:=FailableRealPass[Dummy,F])then UseFn(V)else 0
RecursiveMetadataPass(M:v,R:v,N:int where v:type)<computes>:v=if(N>0)then RecursiveMetadataPass(M,R,N-1)else M
ArgumentRecursiveMetadata(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    UseFn(RecursiveMetadataPass(Dummy,F,1))
RecursiveRealPass(M:v,R:v,N:int where v:type)<computes>:v=if(N>0)then RecursiveRealPass(M,R,N-1)else R
ArgumentRecursiveReal(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    UseFn(RecursiveRealPass(Dummy,F,1))
FieldMetadataPass(M:v,R:v where v:type)<computes>:box(v)=box(v){Value:=M}
ArgumentFieldMetadata(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    UseFn(FieldMetadataPass(Dummy,F).Value)
FieldRealPass(M:v,R:v where v:type)<computes>:box(v)=box(v){Value:=R}
ArgumentFieldReal(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    UseFn(FieldRealPass(Dummy,F).Value)
NamedMetadataPass(M:v,R:v where v:type)<computes>:v=M
ArgumentNamedMetadata(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    UseNamed(?Value:=NamedMetadataPass(Dummy,F))
NamedRealPass(M:v,R:v where v:type)<computes>:v=R
ArgumentNamedReal(F:type{_()<computes>:int},Dummy:type{_()<computes>:int})<computes>:int=
    UseNamed(?Value:=NamedRealPass(Dummy,F))
Main():void=
    Print("DirectMetadata {ArgumentDirectMetadata(One,Two)}")
    Print("DirectReal {ArgumentDirectReal(One,Two)}")
    Print("FailableMetadata {ArgumentFailableMetadata(One,Two)}")
    Print("FailableReal {ArgumentFailableReal(One,Two)}")
    Print("RecursiveMetadata {ArgumentRecursiveMetadata(One,Two)}")
    Print("RecursiveReal {ArgumentRecursiveReal(One,Two)}")
    Print("FieldMetadata {ArgumentFieldMetadata(One,Two)}")
    Print("FieldReal {ArgumentFieldReal(One,Two)}")
    Print("NamedMetadata {ArgumentNamedMetadata(One,Two)}")
    Print("NamedReal {ArgumentNamedReal(One,Two)}")
