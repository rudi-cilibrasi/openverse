# Edge of the case-collision rule (#724): a method Function() and, in a
# subclass, FUNCTION(). The Book has the case commented out
# (FORT-793952...:346, "TODO(SOL-9082)", 9200). OpenVerse measures one
# class's own methods only, and prints
#   lower 42 | upper 420
# If Epic refuses it, a subclass's methods count with its parents'.
base_class := class:
    Function():int = 42

derived_class := class(base_class):
    FUNCTION():int = 420

Main():void =
    Obj := derived_class{}
    Print("OVPROBE lower {Obj.Function()}")
    Print("OVPROBE upper {Obj.FUNCTION()}")
