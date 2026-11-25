# <converges> on a method without a body, of an <abstract> class or an
# interface, is admitted (#724): "The converges effect is only allowed on
# native and abstract functions" (the Book's tests, Effects.versetest:304),
# and UEFN 43.12 admits it (followup-refused/converges-abstract-method).
# On a function with a body it is refused (errors/effect_admission_converges,
# 3565), and no method with a body overrides one (errors/converges_override).
shape := class<abstract>:
    Area()<converges>:int
    Sides<public>()<converges><decides>:int
    Name():string = "shape"
measured := interface:
    Size()<converges>:int
ruler := class<abstract>(shape, measured):
    Name<override>():string = "ruler"
Describe(S:shape):string = S.Name()
Main():void =
    Print("compiled")
