# expect: field 'Pet' of cattery must have the type it inherits, animal, not cat
# a var keeps its type: a write through the class above could store an
# animal that is no cat
animal := class {}
cat := class(animal) {}
shelter := class:
    var Pet:animal = animal{}
cattery := class(shelter):
    var Pet<override>:cat = cat{}
Main():void = Print("ok")
