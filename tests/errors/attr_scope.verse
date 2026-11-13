# expect: @perf is not allowed on a class: the attribute class perf has the scopes @attribscope_function
@attribscope_function
perf := class<computes>(attribute) {}
@perf
thing := class{}
Main():void = {}
