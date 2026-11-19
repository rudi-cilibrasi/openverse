# expect: have names that differ only in case and take the same parameters
# Two <suspends> methods (#724): UEFN 43.12 refuses them with 9002 and 9200
# (followup-book2/case-collision-suspends; the Book's FORT-793952 :67).
cc := class:
    Function()<suspends>:int = 42
    FUNCTION()<suspends>:int = 420
Main()<suspends>:void =
    X := cc{}.Function()
