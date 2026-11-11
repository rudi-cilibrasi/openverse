# Covariant multi-value calls preserve static results and consumer boundaries (#283).
animal := class { N:int=0; Label():string="animal" }
dog := class(animal) { Bark:int=7; Label<override>():string="dog" }
supply := interface:
    Get()<transacts>:animal = animal{N:=1} | animal{N:=2}
special := interface(supply):
    Get<override>()<transacts>:dog = dog{Bark:=4} | dog{Bark:=8}
own := class(special) {}
parent := class(supply):
    Get<override>()<transacts>:dog = dog{Bark:=10} | dog{Bark:=20}
child := class(parent,special) {}
plain := class(supply) {}
Main()<transacts>:void =
    for(D:=own{}.Get()){Print("own {D.Bark}")}
    for(D:=child{}.Get()){Print("child {D.Bark}")}
    Ps:[]supply=array{own{},child{},plain{}}
    for(P:Ps,A:=P.Get()){Print("base {A.Label()}")}
