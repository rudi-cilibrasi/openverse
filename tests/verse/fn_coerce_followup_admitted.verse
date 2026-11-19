# (#724) what UEFN 43.12 (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086) admits of followup-coerce's
# probes, 2026-11-19: functions and methods named where a function type of
# more effects is expected (name-computes-as-transacts, method-value-effect),
# a parameter passed on at its own type (value-computes-as-transacts-control),
# joins of class results and parameters (join-class-result, join-class-param),
# array and tuple literals and case arms that name functions with defaults at
# a type without them (array-of-fns-default, tuple-of-fns-default,
# case-join-default), and generic Identity passed and bound
# (generic-arg-concrete, -generic, -generic-late, generic-bound-first).
animal := class:
    Name():string = "animal"
dog := class(animal):
    Name<override>():string = "dog"
MakeAnimal():animal = animal{}
MakeDog():dog = dog{}
AnyAnimal(A:animal):int = 1
OnlyDog(D:dog):int = 2
Inc(X:int)<computes>:int = X + 1
counter := class:
    Step(X:int)<computes>:int = X + 2
Run(F(:int)<transacts>:int)<transacts>:int = F(1)
Forward(G(:int)<transacts>:int)<transacts>:int = Run(G)
F2(?A:int = 2):int = A
F4(?B:int = 4):int = B
Identity(X:t where t:type):t = X
ApplyInt(F(:int):int, X:int):int = F(X)
Apply(F(:t):t, X:t where t:type):t = F(X)
ApplyLate(X:t, F(:t):t where t:type):t = F(X)
ResultOf(Flag:logic):string =
    F:type{_():animal} = if (Flag?) { MakeDog } else { MakeAnimal }
    F().Name()
ParamOf(Flag:logic):int =
    F:type{_(:dog):int} = if (Flag?) { AnyAnimal } else { OnlyDog }
    F(dog{})
CaseOf(N:int):int =
    F:type{_():int} = case (N):
        1 => F2
        _ => F4
    F()
Main():void =
    T:type{_(:int)<transacts>:int} = Inc
    M:type{_(:int)<transacts>:int} = counter{}.Step
    Print("{T(1)} {M(1)} {Forward(Inc)}")
    Print("{ResultOf(true)} {ResultOf(false)} {ParamOf(true)} {ParamOf(false)}")
    Fs:[]type{_():int} = array{F2, F4}
    P:tuple(type{_():int}, int) = (F2, 1)
    for (F : Fs):
        Print("{F()}")
    Print("{P(0)()} {CaseOf(1)} {CaseOf(2)}")
    B:type{_(:int):int} = Identity
    Print("{ApplyInt(Identity, 1)} {Apply(Identity, 2)} {ApplyLate(3, Identity)} {ApplyInt(B, 4)}")
