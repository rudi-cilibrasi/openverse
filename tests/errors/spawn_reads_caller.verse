# expect: which has the effect <writes>, which its effects (<reads>) do not allow
# (run with --default-rollback, the legacy rule: by default a spawn has the no_rollback effect, which this program's spawn's context excludes, UEFN 43.12 error 3512, #724)
# A spawn has <transacts>'s heap effects: <reads> alone does not allow it
cell:=class{var N:int=0}
Child(H:cell)<suspends><reads>:void=
    Print("read {H.N}")
    Sleep(0.01)
Start(H:cell)<reads>:void=
    T:=spawn{Child(H)}
Main()<suspends>:void=
    Start(cell{})
