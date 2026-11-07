# Wrongly rejected: "K<constructor> calls the default of A, which has the effect
# <writes>". The default of A is the literal 10. The (S:string) overload, which has
# every effect, is the first to leave A to its default; the <computes> one is then
# charged with its effects. Swapping the last two constructors makes it compile
# and print 10 (bug2_ctor_overload_default_effects_ok.verse).
p := class:
    A:int = 10
K<constructor>(X:int) := p:
    A := X
K<constructor>(S:string) := p {}
K<constructor>()<computes> := p {}
Main():void = Print("{K().A}")
