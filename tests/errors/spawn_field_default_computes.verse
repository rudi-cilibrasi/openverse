# expect: starts a task with spawn{…}
# (run with --default-rollback, the legacy rule: by default a spawn has the no_rollback effect, which this program's spawn's context excludes, UEFN 43.12 error 3512, #724)
# A field's default has no more effects than its class declares (Book of
# Verse ch. 13): a <computes> class's default cannot spawn
Child()<suspends><computes>:void=Sleep(0.01)
holder:=class<computes>:
    T:task(void)=spawn{Child()}
Main()<suspends>:void=
    H:=holder{}
    Sleep(0.1)
