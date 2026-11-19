# Book: Tests/ParametricFunctions.versetest:276 (bp_vm_only): Church
# numerals, generic higher-order functions (One, Two) passed as values to
# another (Plus). The Book's Blueprint VM refuses it in code generation (IR
# error 3502, eight times); the Verse VM twin (:288) is valid and agrees in
# OpenVerse, which prints
#   one one 2 | one two 3 | two one 3 | two two 4
# If UEFN 43.12 refuses it (Build Verse Scripts, or the cook of a Verse VM
# session), Epic's shipped toolchain refuses a program OpenVerse runs.
# Control: generic-higher-order-control (One and Two called with Succ, no
# generic function passed).
# Epic's compiler (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086,
# BuildAll, 2026-11-19) refuses it: 3502 (L17) "Using a value of type
# type{_(:type{_(:t)<transacts>:t},:t where t)<transacts>:t} as a value of
# type type{_(:type{_(:int)<transacts>:int},:int)<transacts>:int} i"; 3502
# (L17) "Using a value of type type{_(:type{_(:t)<transacts>:t},:t where
# t)<transacts>:t} as a value of type
# type{_(:type{_(:int)<transacts>:int},:int)<transacts>:int} i"; 3502 (L18)
# "Using a value of type type{_(:type{_(:t)<transacts>:t},:t where
# t)<transacts>:t} as a value of type
# type{_(:type{_(:int)<transacts>:int},:int)<transacts>:int} i"; 3502 (L18)
# "Using a value of type type{_(:type{_(:t)<transacts>:t},:t where
# t)<transacts>:t} as a value of type
# type{_(:type{_(:int)<transacts>:int},:int)<transacts>:int} i"; 3502 (L19)
# "Using a value of type type{_(:type{_(:t)<transacts>:t},:t where
# t)<transacts>:t} as a value of type
# type{_(:type{_(:int)<transacts>:int},:int)<transacts>:int} i"; 3502 (L19)
# "Using a value of type type{_(:type{_(:t)<transacts>:t},:t where
# t)<transacts>:t} as a value of type
# type{_(:type{_(:int)<transacts>:int},:int)<transacts>:int} i"; 3502 (L20)
# "Using a value of type type{_(:type{_(:t)<transacts>:t},:t where
# t)<transacts>:t} as a value of type
# type{_(:type{_(:int)<transacts>:int},:int)<transacts>:int} i"; 3502 (L20)
# "Using a value of type type{_(:type{_(:t)<transacts>:t},:t where
# t)<transacts>:t} as a value of type
# type{_(:type{_(:int)<transacts>:int},:int)<transacts>:int} i".
Zero(F(:t):t, X:t where t:type):t = X
One(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(X)
Two(F(:t)<transacts>:t, X:t where t:type)<transacts>:t = F(F(X))
Plus(A(F(:t)<transacts>:t, X:t)<transacts>:t, B(F(:t)<transacts>:t, X:t)<transacts>:t, F(:t)<transacts>:t, X:t where t:type)<transacts>:t = A(F, B(F, X))
Succ(X:int)<transacts>:int = X + 1

Main():void =
    Print("OVPROBE one one {Plus(One, One, Succ, 0)}")
    Print("OVPROBE one two {Plus(One, Two, Succ, 0)}")
    Print("OVPROBE two one {Plus(Two, One, Succ, 0)}")
    Print("OVPROBE two two {Plus(Two, Two, Succ, 0)}")
