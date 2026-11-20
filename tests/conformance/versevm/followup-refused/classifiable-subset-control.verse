# Control of classifiable-subset: the <castable> class and an array of it,
# without the subset. Not a Book case.
# OpenVerse (ce8632ea, Lean and C agreeing) prints
#   made 1
# If UEFN 43.12 refuses this too, classifiable-subset's refusal is not the
# form's.
base_type := class<castable>{}

Main():void =
    Items:[]base_type = array{base_type{}}
    Print("OVPROBE made {Items.Length}")
