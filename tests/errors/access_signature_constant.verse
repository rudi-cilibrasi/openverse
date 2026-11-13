# expect: Store.Items names Store.item, which is less visible: Store.item is internal to Store
Store<public> := module:
    item := struct:
        N:int = 0
    Items<public>:[]item = array{item{}}
Main():void = {}
