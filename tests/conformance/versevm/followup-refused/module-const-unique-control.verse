# Control of module-const-unique: the objects made in Main, not in module
# constants. Not a Book case.
# OpenVerse (ce8632ea, Lean and C agreeing) prints
#   same and different
# If UEFN 43.12 refuses this too, module-const-unique's refusal is not the
# form's.
unique_allocates_class := class<unique><allocates><computes>{}

Main():void =
    Instance1:unique_allocates_class = unique_allocates_class{}
    Instance2:unique_allocates_class = unique_allocates_class{}
    if (Instance1 = Instance1, Instance1 <> Instance2):
        Print("OVPROBE same and different")
