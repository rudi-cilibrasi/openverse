# Control of constructor-delegation-archetype: the delegation inside a
# constructor function's body. Not a Book case.
# OpenVerse (ce8632ea, Lean and C agreeing) prints
#   label made extra 2
# If UEFN 43.12 refuses this too, constructor-delegation-archetype's refusal
# is not the form's.
base := class:
    Label:string

MakeBase<constructor>(L:string) := base:
    Label := L

derived := class(base):
    Extra:int

MakeDerived<constructor>(E:int) := derived:
    Extra := E
    MakeBase<constructor>("made")

Main():void =
    X := MakeDerived(2)
    Print("OVPROBE label {X.Label} extra {X.Extra}")
