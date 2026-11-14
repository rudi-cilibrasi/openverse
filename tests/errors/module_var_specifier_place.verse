# expect: <persistent> is not allowed on a struct: it is for a class
# <persistent> and <module_scoped_var_weak_map_key> go on classes
s := struct<persistent> {}
Main():void = {}
