# expect: the default of ?C of F constructs reads_class (declared construction budget), which has the effect <reads>, which its effects (<writes>) do not allow
reads_class := class<reads>{}
F(?C:reads_class = reads_class{})<writes>:void = {}
Main():void = {}
