# expect: 4:0: expected '(', ':' or ':=' after 'Y'
# After a `,` at the top level comes a definition, not more of the value.
X:int = 1, Y
Main():void = {}
