# expect: 3:4: node.Walk has several values and is recursive, or called by a recursive one, and it is not <computes>
node := class:
    Walk(N : int)<transacts>:int = N | Walk(N + 1)
leaf := class(node):
    Walk<override>(N : int)<transacts>:int = 0
Main()<transacts>:void =
    for (V := node{}.Walk(0), V > 2):
        Print("{V}")
