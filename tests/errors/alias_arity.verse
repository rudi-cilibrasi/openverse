# expect: 3:0: pair_of takes 1 type argument(s), found 2
pair_of(t:type) := tuple(t, t)
P:pair_of(int, int) = (1, 1)
Main():void = {}
