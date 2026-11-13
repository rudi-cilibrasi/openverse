# expect: Size of Graphics.shape is internal to Graphics
# (Book of Verse ch. 12, "Scoping a Definition Does Not Scope Its Members": error 3593)
Graphics := module:
    shape<scoped{Physics}> := class:
        Size:int = 1
Physics := module:
    using{Graphics}
    Report<public>():int =
        S := shape{}
        S.Size
Main():void = Print("{Physics.Report()}")
