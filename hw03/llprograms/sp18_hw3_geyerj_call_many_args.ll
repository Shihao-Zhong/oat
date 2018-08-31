define i64 @foo(i64 %x1, i64 %x2, i64 %x3, i64 %x4, i64 %x5, i64 %x6, i64 %x7, i64 %x8) {
  %1 = call i64 @bar(i64 1, i64 1, i64 1, i64 1, i64 1, i64 1, i64 1, i64 8, i64 9, i64 10, i64 11)
  %2 = add i64 %1, %x5 
  %3 = add i64 %2, %1 
  ret i64 %1 ; returns sum of args 8, 9, 10, 11
}

define i64 @bar(i64 %x1, i64 %x2, i64 %x3, i64 %x4, i64 %x5, i64 %x6, i64 %x7, i64 %x8, i64 %x9, i64 %x10, i64 %x11) {
  %1 = add i64 %x9, 0
  %2 = add i64 %x10, 0
  %3 = add i64 %x11, 0
  %4 = add i64 %x8, 0
  %5 = call i64 @baz(i64 1, i64 1, i64 1, i64 1, i64 1, i64 1, i64 1, i64 8, i64 %1, i64 %2, i64 %3)
  %6 = add i64 %4, %5
  ret i64 %6 ; returns sum of args 8, 9, 10, 11
}

define i64 @baz(i64 %x1, i64 %x2, i64 %x3, i64 %x4, i64 %x5, i64 %x6, i64 %x7, i64 %x8, i64 %x9, i64 %x10, i64 %x11) {
  %1 = add i64 %x11, %x10
  %2 = add i64 %x9, %1
  ret i64 %2 ; returns sum of args 9, 10, and 11
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @foo(i64 1, i64 2, i64 3, i64 4, i64 5, i64 6, i64 7, i64 8)
  ret i64 %1 ; returns 38
}