# expect: 3:16: unexpected '}'
# Only a `;` may end a braced block: after a `,` an item must follow.
F():int = {1, 2,}
Main():void = {}
