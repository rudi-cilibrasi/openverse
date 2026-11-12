# Covariant multi-value calls preserve static results and consumer boundaries (#283).
animal(t:type) := class<computes> { V:t; Label():string="animal" }
dog(t:type) := class<computes>(animal(t)) { Bark:int=7 }
shelter(t:type) := interface:
    Get()<computes>:animal(t)
kennel := class(shelter(int)):
    Get<override>()<computes>:dog(int) = dog(int){V:=1} | dog(int){V:=2}
Unused(P:shelter(string),N:int)<computes>:animal(string) = if(N>0) then (P.Get()|Unused(P,N-1)) else animal(string){V:="end"}
Main():void = Print("alive")
