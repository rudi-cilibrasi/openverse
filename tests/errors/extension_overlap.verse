# expect: 5:0: the extension method AddScalar is defined twice with parameters a call cannot tell apart, ([]int, int) and ([int]int, int): overloads must take disjoint types
# Overloads of an extension method a call could not tell apart: an array
# and a map share the empty one (Book of Verse tests, error 3532)
(A:[]int).AddScalar(B:int):[]int = for (X : A) { X + B }
(A:[int]int).AddScalar(B:int):[]int = for (K -> X : A) { X + B }
Main():void = {}
