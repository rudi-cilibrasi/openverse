# expect: 4:32: Collect calls D, which has the effect <reads>, which its effects (<computes>) do not allow
# (an inlined call of a function with several values still needs its declared effects)
D()<reads>:int = 1 | 2
Collect()<computes>:[]int = for{D()}
Main():void = Print("{Collect().Length}")
