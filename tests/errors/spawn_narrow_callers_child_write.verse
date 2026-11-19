# expect: do not allow
# (run with --default-rollback, the legacy rule: by default a spawn has the no_rollback effect, which this program's spawn's context excludes, UEFN 43.12 error 3512, #724)
cell:=class{var N:int=0}
Child(H:cell)<suspends><writes>:void=
    set H.N=7
    Sleep(0.1)
Start(H:cell)<computes>:void=
    T:=spawn{Child(H)}
Main()<suspends>:void=Start(cell{})
