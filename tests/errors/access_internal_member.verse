# expect: Secret of Vault.box is internal to Vault: mark it <public> to use it outside
# (Book of Verse ch. 10: a member is internal by default; AccessLevelInheritance.versetest:835)
Vault := module:
    box<public> := class:
        Secret:int = 7
    Make<public>():box = box{}
Main():void = Print("{Vault.Make().Secret}")
