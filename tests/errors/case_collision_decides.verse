# expect: have names that differ only in case and take the same parameters
# <decides> does not tell them apart, nor do other effects or access
# specifiers (#724; the Book's FORT-793952 :73, :79, :85, bp_vm_only, and
# UEFN 43.12's 9200 for the plain pair, followup-book2/case-collision-module-fn)
mm := module:
    Function<public>()<decides>:int = 42
    FUNCTION<public>():int = 420
Main():void = Print("{mm.FUNCTION()}")
