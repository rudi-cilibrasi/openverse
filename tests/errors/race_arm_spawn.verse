# expect: this arm of race cannot suspend
# A spawn starts a task and goes on: an arm that only spawns cannot suspend
Wait()<suspends>:void =
    Sleep(1.0)
Main()<suspends>:void =
    race:
        Wait()
        block:
            spawn{Wait()}
