# expect: c is below base, which is <final_super_base>, so it must be <final_super>
base := class<final_super_base> {}
c := class(base) {}
Main():void = {}
