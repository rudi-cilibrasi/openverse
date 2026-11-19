# expect: derived.F overrides base.F, whose type has base's type parameter t inside a function type
# (#724) an override, in a class of base(int), of a parametric class's
# method whose parameter is a function of t (UEFN 43.12, ++Fortnite+Release-43.12-CL-60598086, error 3502,
# "Using a value of type (int->void)->void as a value of type
# (any->void)->void": followup-coerce/class-override-fn-param).
TheG(X:int):void = {}
base(t:type) := class:
    F(G(:t):void):void = {}
derived := class(base(int)):
    F<override>(G(:int):void):void = G(1)
Main():void =
    derived{}.F(TheG)
