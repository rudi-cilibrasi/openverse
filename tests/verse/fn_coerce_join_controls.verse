# (#724) branches of an if that need no wrapper at the if's function type:
# the same type (Tuple.versetest:456's ArrayToString, followup-book2's
# join-named-tuple: Epic reports the other branch only), a function returning
# a subclass (the Book of Verse's FunctionTypes.versetest 198-203, valid on
# both VMs), a named parameter defaulted in one and not in the other, at the
# type without the default (DefaultNamed.versetest:623, valid on both VMs),
# and a function of a parameter of such a type (DefaultNamed.versetest 731,
# 735).
c2 := class { Name():string = "C2" }
c3 := class(c2) { Name<override>():string = "C3" }
F13():c2 = c2{}
F14():c3 = c3{}
F1(?A:int):int = A
F2(?A:int = 2):int = A
G1(F(?A:int):int):int = F(?A := 1)
G2(F(?A:int = 0):int):int = F() + F(?A := 2)
F6(?A:int = 6):int = A
P(Flag:logic):string =
    G := if (Flag?) { F13 } else { F14 }
    G().Name()
Q(Flag:logic):int =
    F:type{_(?A:int):int} = if (Flag?) { F1 } else { F2 }
    F(?A := 5)
R(Flag:logic):int =
    F:type{_(G(?A:int = 0):int):int} = if (Flag?) { G1 } else { G2 }
    F(F6)
Main():void =
    Print("{P(true)} {P(false)} {Q(true)} {Q(false)} {R(true)} {R(false)}")
