# expect: which has the effect <writes>, which its effects (<allocates>) do not allow
# A spawn has <transacts>'s heap effects: <allocates> alone does not allow it
token:=class<allocates><unique>{V:int}
Child(N:int)<suspends><allocates>:void=
    Obj:=token{V:=N}
    Sleep(0.01)
Main()<allocates>:void=
    T:=spawn{Child(1)}
