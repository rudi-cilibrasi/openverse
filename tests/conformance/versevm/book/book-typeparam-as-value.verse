# Book: Tests/TypeParam.versetest:49 (verse_vm_only, assert_valid): a type
# parameter passed as a value of type type.
Bar(t:type):void = {}
Foo(:t where t:type):void = Bar(t)

Main():void =
    Foo(1)
    Print("OVPROBE called")
