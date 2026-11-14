# expect: 4:43: cannot infer type parameter t of ReplaceAll from the arguments of this call
# The helper's type parameter by its name, not as openverse renames it; the
# Book's tests expect this call to succeed (ArrayReplaceAll.versetest:12).
Main()<decides>:void = {array{}.ReplaceAll(array{}, array{}) = array{}}
