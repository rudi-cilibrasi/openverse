# expect: 3:37: return cannot leave a failure context
# A return in the clauses of first{} (a failure context, Book of Verse ch. 8)
F(X:int)<decides>:int = first{X > 0; return 7}
Main():void = if (V := F[1]) then Print("{V}")
