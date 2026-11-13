# expect: t, a type parameter, given as Bar's type argument t: openverse takes the BPVM's reading, a link error
Bar(t:type):?t = false
Foo(X:t where t:type):?t = Bar(t)
Main():void = {}
