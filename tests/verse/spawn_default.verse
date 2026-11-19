# (run with --default-rollback, the legacy rule: by default a spawn has the no_rollback effect, which this program's spawn's context excludes, UEFN 43.12 error 3512, #724)
# a field's default may spawn: the task starts at each construction that omits the field (#156)
Tick(Name:string, N:int)<suspends>:int =
    var I:int = 0
    loop:
        if (I >= N) then break
        Sleep(1.0)
        set I += 1
        Print("{Name} {I}")
    N
worker := class:
    Name:string
    Job:task(int) = spawn{Tick("default", 2)}
Main()<suspends>:void =
    W := worker{Name := "w"}
    V := worker{Name := "v", Job := spawn{Tick("given", 1)}}
    Print("{W.Name} {W.Job.Await()} {V.Name} {V.Job.Await()}")
