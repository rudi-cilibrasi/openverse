# expect: expected int, found string
# (run with --default-rollback, the legacy rule: by default a spawn has the no_rollback effect, which this program's spawn's context excludes, UEFN 43.12 error 3512, #724)
base(t:type) := class:
    Go(?N:int=0)<suspends>:void=Print("base")
ib := class(base(int)):
    Go<override>(?N:int="bad")<suspends>:void=Print("body {N}")
AsBase(P:base(t) where t:type):base(t)=P
unused := struct:
    T:task(void)=spawn{AsBase(ib{}).Go()}
Main():void=Print("unused")
