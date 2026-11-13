# expect: Make names secret, which is less visible: secret is internal to the top level
# (a public function's result type: DigestVisibility.versetest:72-106)
secret := class:
    N:int = 1
Make<public>():?secret = false
Main():void = {}
