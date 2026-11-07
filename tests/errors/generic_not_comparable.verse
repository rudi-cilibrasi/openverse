# expect: type parameter t of Has must be comparable, and u is not: declare u:subtype(comparable)
Has(A:[]t, X:t where t:subtype(comparable))<decides>:void = A.Find[X]

Wrap(A:[]u, X:u where u:type)<decides>:void = Has[A, X]

Main():void = Print("never called")
