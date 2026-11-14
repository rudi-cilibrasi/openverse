# expect: thing is <concrete>, so its field 'Field' needs a default
# re-declaring a field with no value does not give it one (Book of Verse
# ch. 10, "Concrete": "Re-declaring the member with `<override>` does not
# satisfy the requirement — it still needs an initializer")
has_field := interface:
    Field:int
thing := class<concrete>(has_field):
    Field<override>:int
Main():void = Print("ok")
