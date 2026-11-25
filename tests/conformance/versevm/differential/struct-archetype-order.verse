# The order in which a struct archetype's field values are evaluated when
# they are written in another order than the fields are declared.
# Tests LANGUAGE.md, Supported, Structs: "name{F := e, ...} (each field given
# at most once, evaluated in declaration order ...; ... the clauses and the
# field values run in the order written)". The fields are declared A, B, C
# and given C, A, B; each value is printed as it is computed.
# OpenVerse (#724) printed, until Epic's result below (declaration order):
#   value a | value b | value c | done 123
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-20) printed
#   value c | value a | value b | done 123
# the order written. OpenVerse now prints it too (#724, Lean and C agreeing).
Note(S:string, V:int):int =
    Print("OVPROBE value {S}")
    V

trio := struct:
    A:int
    B:int
    C:int

Main():void =
    T := trio{C := Note("c", 3), A := Note("a", 1), B := Note("b", 2)}
    Print("OVPROBE done {T.A}{T.B}{T.C}")
