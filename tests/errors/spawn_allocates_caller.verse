# expect: which has the effect <writes>, which its effects (<allocates>) do not allow
# (run with --default-rollback, the legacy rule: by default a spawn has the no_rollback effect, which this program's spawn's context excludes, UEFN 43.12 error 3512, #724)
# A spawn has <transacts>'s heap effects: <allocates> alone does not allow it
token:=class<allocates><unique>{V:int}
Child(N:int)<suspends><allocates>:void=
    Obj:=token{V:=N}
    Sleep(0.01)
Main()<allocates>:void=
    T:=spawn{Child(1)}
