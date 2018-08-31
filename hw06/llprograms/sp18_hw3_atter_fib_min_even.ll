define i64 @fib(i64 %a, i64 %b, i64 %n) {
  %1 = add i64 %a, %b
  %2 = sub i64 %n, 1
  %3 = icmp sgt i64 %2, 1
  br i1 %3, label %again, label %end
again:
  %4 = call i64 @fib(i64 %b, i64 %1, i64 %2)
  ret i64 %4
end:
  ret i64 %1
}

define i64 @min(i64 %a, i64 %b) {
  %1 = icmp sgt i64 %a, %b
  br i1 %1, label %retb, label %reta
reta:
  ret i64 %a
retb:
  ret i64 %b
}

define i64 @iseven(i64 %n) {
  %1 = icmp eq i64 %n, 0
  br i1 %1, label %evenendt, label %evenisf
evenisf:
  %2 = icmp sgt i64 %n, 0
  br i1 %2, label %evenloop, label %evenendf
evenloop:
  %3 = sub i64 %n, 2
  %4 = call i64 @iseven(i64 %3) 
  ret i64 %4
evenendt:
  ret i64 1
evenendf:
  ret i64 0
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @fib(i64 0, i64 1, i64 5)
  %2 = call i64 @min(i64 5, i64 9)
  %3 = call i64 @iseven(i64 5)
  %4 = call i64 @iseven(i64 4)
  %5 = call i64 @iseven(i64 0)
  %6 = add i64 %1, %2
  %7 = add i64 %3, %4
  %8 = add i64 %6, %7
  %9 = add i64 %8, %5
  ret i64 %9 ; Should equal 12
}