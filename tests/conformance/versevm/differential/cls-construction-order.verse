# The order of a construction: the archetype's field values as written, the
# block clauses of the class and of its parent, and what the blocks see.
# Tests LANGUAGE.md, Classes, block: "A class's block: clauses run when an
# instance is constructed, after its fields are given, those of the classes
# above it first, each class's in order"; Accessors, Order: "A construction
# evaluates its fields' values in the order they are declared". The
# archetype below gives B before A, each value printed as it is computed.
# OpenVerse (#724) printed, until Epic's result below (the fields' values in
# declaration order):
#   value a | value b | base block A 10 | derived block one B 20
#   derived block two A 10 | done 10 20
# Epic's Verse VM (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, "Use
# Verse VM" on, 2026-11-20) printed
#   value b | value a | base block A 10 | derived block one B 20
#   derived block two A 10 | done 10 20
# the fields given are evaluated in the order written, then the blocks from
# the top. OpenVerse now prints it too (#724, Lean and C agreeing; an omitted
# default's place among given values is not asked here).
Note(S:string, V:int):int =
    Print("OVPROBE value {S}")
    V

base_cls := class:
    A:int = 1
    block:
        Print("OVPROBE base block A {A}")

derived_cls := class(base_cls):
    B:int = 2
    block:
        Print("OVPROBE derived block one B {B}")
    block:
        Print("OVPROBE derived block two A {A}")

Main():void =
    D := derived_cls{B := Note("b", 20), A := Note("a", 10)}
    Print("OVPROBE done {D.A} {D.B}")
