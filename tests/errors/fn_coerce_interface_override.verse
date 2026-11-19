# expect: using a value of type type{_(:type{_(:int):void})<transacts>:void} as a value of type type{_(:type{_(:any):void})<transacts>:void} is not yet implemented: b.F overrides a.F
# b, a class of a(int), overrides a's F(G(:t):void): a call through the
# declaration, whose t is any there, needs a wrapper that converts the
# function G, which Epic's Verse compiler does not make (UEFN 43.12, error
# 3502, "Using a value of type type{_(:int->void)<transacts>:void} as a value
# of type type{_(:any->void)<transacts>:void}":
# followup-book2/interface-fn-param-generic; the Book of Verse's
# SOL-5477-CrashInGenClassDefinition.versetest:5, bp_vm_only). F(X:t) is
# admitted (fn_coerce_interface_param_control).
TheG(X:int):void = {}
a(t:type) := interface:
    F(G(:t):void)<transacts>:void
b := class(a(int)):
    F<override>(G(:int):void)<transacts>:void = {}
Main():void =
    Obj:b = b{}
    Obj.F(TheG)
