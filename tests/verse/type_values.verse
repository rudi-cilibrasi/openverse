# Types as values (Book of Verse ch. 11; its tests, Subtype.versetest,
# Cast.versetest 90-150, MetatypeConcreteSubtype.versetest): a class named
# as a value, of subtype(…), castable_subtype(…), concrete_subtype(…) and
# type; subtype(A) below subtype(B) when A is below B; a cast through a type
# value, T[X]; a construction through one, T{}; a join of two at the
# nearest metatype above both
C0 := class {}
C1 := class(C0) {}
C2 := class:
    var m0:subtype(C0)
    var m1:subtype(C2)
    f0():void={set m0 = C0}
    f1():void={set m0 = C1}
    f3(classArg:subtype(C0)):void={set m0 = classArg}
    f4(classArg:subtype(C1)):void={set m0 = classArg}
base := class{ N:int = 0 }
class1 := class(base) { N<override>:int = 1 }
class2 := class(class1) { N<override>:int = 2 }
classA := class(base){ N<override>:int = 10 }
classB := class(classA){ N<override>:int = 11 }
Pick(B:logic, X:base):int =
    t := if (B?) then class2 else classB
    if (Y := t[X]) then Y.N else -1
Make(T:concrete_subtype(base)):int = T{}.N
CC0 := class<castable> {}
CC1 := class(CC0) {}
CC2 := class<castable>:
    var m0:castable_subtype(CC0)
    f1():void={set m0 = CC1}
T0 := interface { ft0():int }
T1 := interface(T0) { ft1():int }
CT0 := class(T0):
    var mt0:subtype(T0)
    ft0<override>():int = 0
CT1 := class(T1):
    ft0<override>():int = 10
    ft1<override>():int = 11
Upcast(c:subtype(CT1)):type = c
Names(X:T0, T:subtype(T0)):int = if (Y := T[X]) then Y.ft0() else -1
Main():void =
    c2 := C2{m0 := C1, m1 := C2}
    c2.f0(); c2.f1(); c2.f3(C0); c2.f4(C1)
    Print("{Pick(true, class2{})} {Pick(false, class2{})} {Pick(true, classB{})} {Pick(false, classB{})}")
    Print("{Make(class2)} {Make(classA)} {Make(base)}")
    cc2 := CC2{m0 := CC1}
    cc2.f1()
    ct0 := CT0{mt0 := CT1}
    L0:subtype(T1) = CT1
    L1:subtype(T0) = L0
    Z := Upcast(CT1)
    Print("{Names(CT1{}, L1)} {Names(ct0, L1)} {Names(ct0, CT0)} {Names(ct0, CT1)}")
