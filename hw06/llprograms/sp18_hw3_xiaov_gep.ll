%pair = type { i64, %var*}
%var = type { [3 x i64] }
%map = type [10 x %pair]

@g_map = global %map [ 
	%pair { i64 13, %var* null },
	%pair { i64 0, %var* null },
	%pair { i64 0, %var* null },
	%pair { i64 0, %var* null },
	%pair { i64 0, %var* null },
	%pair { i64 0, %var* null },
	%pair { i64 0, %var* null },
	%pair { i64 0, %var* null },
	%pair { i64 0, %var* null },
	%pair { i64 0, %var* null }
]

@var_inst = global %var { [3 x i64] [i64 0, i64 0, i64 0] }


define i64 @main(i64 %argc, i8** %arcv) {
	call %var* @alloc_var(i64 1, i64 2, i64 3)
	call %var* @alloc_var(i64 4, i64 5, i64 6)

	call void @put_0(i64 1, %var* @var_inst)

	%var_p = call %var* @get_val_0()
	%ans = call i64 @get_var_c(%var* %var_p)

  	ret i64 %ans
}

define void @alloc_var(i64 %a, i64 %b, i64 %c) {
	%p_a = getelementptr %var, %var* @var_inst, i32 0, i32 0, i32 0
	store i64 %a, i64* %p_a

	%p_b = getelementptr %var, %var* @var_inst, i32 0, i32 0, i32 1
	store i64 %b, i64* %p_b

	%p_c = getelementptr %var, %var* @var_inst, i32 0, i32 0, i32 2
	store i64 %c, i64* %p_c

	ret void
}

define void @put_0(i64 %key, %var* %val) {

	%p_k = getelementptr %map, %map* @g_map, i32 0, i32 0, i32 0
	store i64 %key, i64* %p_k

	%p_v = getelementptr %map, %map* @g_map, i32 0, i32 0, i32 1
	store %var* %val, %var** %p_v

  	ret void
}

define %var* @get_val_0() {
	%var_p = getelementptr %map, %map* @g_map, i32 0, i32 0, i32 1
	%ret = load %var*, %var** %var_p

	ret %var* %ret
}

define i64 @get_var_c(%var* %addr) {
	%p_c = getelementptr %var, %var* %addr, i32 0, i32 0, i32 2
	%ret = load i64, i64* %p_c

	ret i64 %ret
}