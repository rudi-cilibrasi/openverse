# expect: 4:0: expected an indented function body
# A ':' body may be empty, but '=' needs a body: an expression, a block.
F():void =
Main():void = F()
