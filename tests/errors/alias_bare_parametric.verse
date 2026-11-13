# expect: 3:0: pair_of is parametric: write pair_of(…) with 1 type argument(s)
pair_of(t:type) := tuple(t, t)
P:pair_of = (1, 1)
Main():void = {}
