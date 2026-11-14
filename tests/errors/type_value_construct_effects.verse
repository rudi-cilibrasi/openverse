# expect: e.F constructs through T, a concrete_subtype(c), which may construct d (declared construction budget), which has the effect <writes>
# T{} may construct any <concrete> class below c, so it has their
# construction effects (Book of Verse tests,
# SOL-8627-concrete_subtype-effects.versetest: "Could invoke d's
# constructor", 3512)
c := class<reads> {}
d := class<concrete><reads><writes>(c) {}
e := class:
    T:concrete_subtype(c)
    F()<reads>:c = T{}
Main():void = Print("ok")
