@glist = global [10 x i64] [ i64 10, i64 4, i64 6, i64 2, i64 5, i64 1, i64 3, i64 9, i64 7, i64 8 ]

define i64 @is_sorted([10 x i64]* %list, i64 %i1, i64 %i2) {
  %at_end = icmp sge i64 %i2, 9
  br i1 %at_end, label %end, label %compare
compare:
  %ptr1 = getelementptr [10 x i64], [10 x i64]* %list, i32 0, i64 %i1
  %ptr2 = getelementptr [10 x i64], [10 x i64]* %list, i32 0, i64 %i2
  %val1 = load i64, i64* %ptr1
  %val2 = load i64, i64* %ptr2
  %less = icmp sle i64 %val1, %val2
  br i1 %less, label %true, label %false
true:
  %i3 = add i64 %i2, 1
  %ret_value = call i64 @is_sorted([10 x i64]* @glist, i64 %i2, i64 %i3)
  ret i64 %ret_value
false: 
  ret i64 0
end: 
  ret i64 1
}

define i64 @selectionsort([10 x i64]* %list, i64 %n) {
  %at_end = icmp eq i64 %n, 9 
  br i1 %at_end, label %fin, label %setup_check_min
setup_check_min:
  %i = alloca i64
  %min = alloca i64
  %min_index = alloca i64
  store i64 %n, i64* %i
  %min_ptr = getelementptr [10 x i64], [10 x i64]* %list, i32 0, i64 %n
  %min_value = load i64, i64* %min_ptr
  store i64 %min_value, i64* %min
  store i64 %n, i64* %min_index
  br label %check_min
check_min:
  %i_val = load i64, i64* %i
  %ptr1 = getelementptr [10 x i64], [10 x i64]* %list, i32 0, i64 %i_val
  %min_val = load i64, i64* %min
  %cur_val = load i64, i64* %ptr1
  %less_than = icmp slt i64 %cur_val, %min_val
  br i1 %less_than, label %set_min, label %check_at_end
set_min:
  store i64 %cur_val, i64* %min
  store i64 %i_val, i64* %min_index
  br label %check_at_end
check_at_end:
  %at_end1 = icmp eq i64 %i_val, 9
  br i1 %at_end1, label %swap, label %inc_i
inc_i:
  %next_i = add i64 %i_val, 1
  store i64 %next_i, i64* %i
  br label %check_min
swap:
  %n_ptr = getelementptr [10 x i64], [10 x i64]* %list, i32 0, i64 %n
  %m_index = load i64, i64* %min_index
  %other_ptr = getelementptr [10 x i64], [10 x i64]* %list, i32 0, i64 %m_index
  %m_val = load i64, i64* %other_ptr
  %val = load i64, i64* %n_ptr
  store i64 %m_val, i64* %n_ptr
  store i64 %val, i64* %other_ptr
  br label %cont
cont:
  %next_n = add i64 %n, 1
  %y = call i64 @selectionsort([10 x i64]* @glist, i64 %next_n)
  ret i64 %y
fin:
  ret i64 1
}

define i64 @main(i64 %argc, i8** %arcv) {
  call i64 @selectionsort([10 x i64]* @glist, i64 0)
  %x = call i64 @is_sorted([10 x i64]* @glist, i64 0, i64 1)
  ret i64 %x
}