# expect: field 'Next' of bi_list names bi_list(u, t), bi_list at other type arguments than its own: a parametric type refers to itself only as bi_list(t, u)
# the same parameters in another order are other type arguments
bi_list(t:type, u:type) := class:
    Value:t
    Next:?bi_list(u, t)
Main():void = Print("ok")
