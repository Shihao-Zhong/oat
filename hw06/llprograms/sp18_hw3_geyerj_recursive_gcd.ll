define i64 @gcd(i64 %x, i64 %y) {
  %cmp = icmp eq i64 %x, %y
  br i1 %cmp, label %x_ret, label %get_smaller
get_smaller:
  %cmp1 = icmp slt i64 %x, %y
  br i1 %cmp1, label %x_smaller, label %y_smaller
x_smaller:
  %cmpx = icmp eq i64 %x, 0
  br i1 %cmpx, label %y_ret, label %x_rec
x_rec:
  %new_y = sub i64 %y, %x
  %rec_x_call = call i64 @gcd(i64 %x, i64 %new_y)
  ret i64 %rec_x_call
y_smaller:
  %cmpy = icmp eq i64 %y, 0
  br i1 %cmpy, label %x_ret, label %y_rec
y_rec:
  %new_x = sub i64 %x, %y
  %rec_y_call = call i64 @gcd(i64 %new_x, i64 %y)
  ret i64 %rec_y_call
x_ret:
  ret i64 %x
y_ret:
  ret i64 %y
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @gcd(i64 17, i64 51)
  %2 = call i64 @gcd(i64 128, i64 48)
  %3 = add i64 %1, %2 
  ret i64 %3
}