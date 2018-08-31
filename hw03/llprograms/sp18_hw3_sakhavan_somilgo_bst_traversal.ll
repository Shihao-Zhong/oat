%arr = type [10 x i64]

@aux = global %arr [ i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 1, i64 0, i64 0, i64 0]

%tree = type {%tree*, i64, %tree*}

@null = global %tree {%tree* null, i64 -1, %tree* null}
@l1 = global %tree {%tree* @null, i64 2, %tree* @null}
@l2 = global %tree {%tree* @null, i64 5, %tree* @null}
@l3 = global %tree {%tree* @null, i64 9, %tree* @null}
@l4 = global %tree {%tree* @null, i64 11, %tree* @null}
@l5 = global %tree {%tree* @null, i64 19, %tree* @null}
@p1 = global %tree {%tree* @l1, i64 4, %tree* @l2}
@p2 = global %tree {%tree* @p1, i64 7, %tree* @l3}
@p3 = global %tree {%tree* @l4, i64 18, %tree* @l5}
@p4 = global %tree {%tree* @p3, i64 20, %tree* @null}
@root = global %tree {%tree* @p2, i64 10, %tree* @p4}

define i64 @is_sorted(%arr* %ptr, i64 %size, i64 %idx) {
	%size_minus_1 = sub i64 %size, 1
	%base_case = icmp sge i64 %idx, %size_minus_1
	br i1 %base_case, label %return_true, label %check
	return_true:
		ret i64 1
	check:
		%n_1p = getelementptr %arr, %arr* %ptr, i32 0, i64 %idx
		%idx_plus_1 = add i64 %idx, 1
		%n_2p = getelementptr %arr, %arr* %ptr, i32 0, i64 %idx_plus_1
		%n_1 = load i64, i64* %n_1p
		%n_2 = load i64, i64* %n_2p
		%compare_n1_n2 = icmp sle i64 %n_1, %n_2
		br i1 %compare_n1_n2, label %move_ptr, label %return_false
	return_false:
		ret i64 0
	move_ptr:
		%iter = call i64 @is_sorted(%arr* %ptr, i64 %size, i64 %idx_plus_1)
		ret i64 %iter
}

define i64 @inorder (%tree* %mid, i64 %idx)
{
	%mid_valp = getelementptr %tree, %tree* %mid, i32 0, i32 1
	%mid_val = load i64, i64* %mid_valp
	%is_null = icmp eq i64 %mid_val, -1
	br i1 %is_null, label %done, label %not_done
	done: 
		ret i64 %idx
	not_done:
		%leftp = getelementptr %tree, %tree* %mid, i32 0, i32 0
		%left = load %tree*, %tree** %leftp
		%out1 = call i64 @inorder(%tree* %left, i64 %idx)
		%arr_drop = getelementptr %arr, %arr* @aux, i32 0, i64 %out1
		store i64 %mid_val, i64* %arr_drop
		%new_idx = add i64 %out1, 1
		%rightp = getelementptr %tree, %tree* %mid, i32 0, i32 2
		%right = load %tree*, %tree** %rightp
		%out2 = call i64 @inorder(%tree* %right, i64 %new_idx)
		ret i64 %out2
}

define i64 @main(i64 %argc, i8** %arcv) {
	%done = call i64 @inorder(%tree* @root, i64 0)
	%result = call i64 @is_sorted(%arr* @aux, i64 10, i64 0)
	ret i64 %result
}