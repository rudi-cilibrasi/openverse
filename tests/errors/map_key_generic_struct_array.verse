# expect: a map key cannot be or hold an array or a map: p([]int) holds []int
# (a parametric struct's fields at its type arguments: "The restriction
# travels with the array", Book of Verse ch. 3)
p(t:type) := struct{X:t}
Main():void =
    M:[p([]int)]int = map{}
