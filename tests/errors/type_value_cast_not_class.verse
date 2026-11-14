# expect: 6:14: a cast through query_type, of type subtype(int), would cast to int, which is no class or interface
# A cast through a type value of subtype(int) (the Book's tests, SOL-7475,
# 3509): said in the source's terms, not as the method openverse writes.
unique_entity := class<unique><castable>(){}
Func(query_type:subtype(int))<decides>:void =
    query_type[unique_entity{}] = unique_entity{}
Main():void = {}
