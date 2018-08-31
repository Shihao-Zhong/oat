%arr = type [20 x i64]

@glist = global %arr [ i64 7, i64 6, i64 15, i64 11, i64 5, 
                       i64 8, i64 12, i64 1, i64 20, i64 19, 
                       i64 18, i64 17, i64 13, i64 10, i64 9, 
                       i64 16, i64 2, i64 3, i64 4, i64 14 ]

define void @qsort(%arr* %a, i64 %lo, i64 %hi) {
  %exit_cond = icmp slt i64 %lo, %hi
  br i1 %exit_cond, label %do_start, label %exit
do_start:
  %l = alloca i64
  %h = alloca i64
  store i64 %lo, i64* %l
  store i64 %hi, i64* %h
  %p_ptr = getelementptr %arr, %arr* %a, i32 0, i64 %hi
  %p = load i64, i64* %p_ptr
  br label %increment_l_cond
increment_l_cond:
  %l1 = load i64, i64* %l
  %h1 = load i64, i64* %h
  %l_lt_h = icmp slt i64 %l1, %h1
  br i1 %l_lt_h, label %l_second_cond, label %decrement_h_cond
l_second_cond:
  %ptr_a_l = getelementptr %arr, %arr* %a, i32 0, i64 %l1
  %a_l = load i64, i64* %ptr_a_l
  %a_l_le_p = icmp sle i64 %a_l, %p
  br i1 %a_l_le_p, label %increment_l_body, label %decrement_h_cond
increment_l_body:
  %l_plus_1 = add i64 %l1, 1
  store i64 %l_plus_1, i64* %l
  br label %increment_l_cond
decrement_h_cond:
  %l2 = load i64, i64* %l
  %h2 = load i64, i64* %h
  %h_gt_l = icmp sgt i64 %l2, %h2
  br i1 %h_gt_l, label %h_second_cond, label %if_cond
h_second_cond:
  %ptr_a_h = getelementptr %arr, %arr* %a, i32 0, i64 %h2
  %a_h = load i64, i64* %ptr_a_h
  %a_h_ge_p = icmp sge i64 %a_h, %p
  br i1 %a_h_ge_p, label %decrement_h_body, label %if_cond
decrement_h_body:
  %h_minus_1 = sub i64 %h2, 1
  store i64 %h_minus_1, i64* %h
  br label %decrement_h_cond
if_cond:
  %l3 = load i64, i64* %l
  %h3 = load i64, i64* %h
  %l_lt_h_2 = icmp slt i64 %l3, %h3
  br i1 %l_lt_h_2, label %if_body, label %do_while_exit
if_body:
  %ptr_a_h2 = getelementptr %arr, %arr* %a, i32 0, i64 %h2
  %a_h2 = load i64, i64* %ptr_a_h2
  store i64 %a_l, i64* %ptr_a_h2
  store i64 %a_h2, i64* %ptr_a_l
  br label %do_start
do_while_exit:
  %ptr_a_l3 = getelementptr %arr, %arr* %a, i32 0, i64 %l1
  %a_l3 = load i64, i64* %ptr_a_l3
  %ptr_a_h3 = getelementptr %arr, %arr* %a, i32 0, i64 %h2
  %a_h3 = load i64, i64* %ptr_a_h3
  store i64 %a_h3, i64* %p_ptr
  store i64 %p, i64* %ptr_a_l3
  %call_hi = sub i64 %l3, 1
  %call_lo = add i64 %l3, 1
  call void @qsort(%arr* %a, i64 %call_lo, i64 %hi)
  call void @qsort(%arr* %a, i64 %lo, i64 %call_hi)
  br label %exit
exit:
  ret void
}

define i64 @is_sorted(%arr* %a, i64 %size) {
  %base_case = icmp sle i64 %size, 1
  br i1 %base_case, label %return_1, label %check
return_1:
  ret i64 1
check:
  %n_minus_1 = sub i64 %size, 1
  %n_minus_2 = sub i64 %size, 2
  %ptr_fst = getelementptr %arr, %arr* %a, i32 0, i64 %n_minus_1
  %ptr_snd = getelementptr %arr, %arr* %a, i32 0, i64 %n_minus_2
  %fst = load i64, i64* %ptr_fst
  %snd = load i64, i64* %ptr_snd
  %out_of_order = icmp slt i64 %fst, %snd
  br i1 %out_of_order, label %return_0, label %recurse
return_0:
  ret i64 0
recurse:
  %result = call i64 @is_sorted(%arr* %a, i64 %n_minus_1)
  ret i64 %result
}

define i64 @main(i64 %argc, i8** %arcv) {
  %already_sorted = call i64 @is_sorted(%arr* @glist, i64 20)
  %early_failure = icmp eq i64 %already_sorted, 1
  br i1 %early_failure, label %ret_2, label %sort
ret_2:
  ret i64 2
sort:
  call void @qsort(%arr* @glist, i64 0, i64 19)
  %result = call i64 @is_sorted(%arr* @glist, i64 20)
  ret i64 %result
}