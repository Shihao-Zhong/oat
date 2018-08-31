%buffer_t = type [50 x i64]

@buffer = global %buffer_t [
    i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0,
    i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0,
    i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0,
    i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0,
    i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0, i64 0
]

define i64 @nth_prime(i64 %n) {
  %p0 = getelementptr %buffer_t, %buffer_t* @buffer, i32 0, i32 0
  %p1 = getelementptr %buffer_t, %buffer_t* @buffer, i32 0, i32 1
  %p2 = getelementptr %buffer_t, %buffer_t* @buffer, i32 0, i32 2
  %p3 = getelementptr %buffer_t, %buffer_t* @buffer, i32 0, i32 3

  store i64 2, i64* %p0
  store i64 3, i64* %p1
  store i64 5, i64* %p2
  store i64 7, i64* %p3

  %found = alloca i64
  %curr = alloca i64
  store i64 4, i64* %found
  store i64 6, i64* %curr

  br label %while_start

while_start:
  %1 = load i64, i64* %found
  %2 = icmp slt i64 %1, %n
  br i1 %2, label %while_body, label %while_end

while_body:
  %is_prime = alloca i64
  %i = alloca i64
  store i64 1, i64* %is_prime
  store i64 0, i64* %i
  br label %for_start

for_start:
  %ival = load i64, i64* %i
  %13 = load i64, i64* %found
  %14 = load i64, i64* %is_prime
  %15 = icmp slt i64 %ival, %13
  %16 = icmp eq i64 %14, 1

  br i1 %15, label %for_cnd_2, label %for_exit

for_cnd_2:
  br i1 %16, label %for_body, label %for_exit

for_body:
  %pptr = getelementptr %buffer_t, %buffer_t* @buffer, i32 0, i64 %ival
  %p = load i64, i64* %pptr
  %test = alloca i64
  store i64 %p, i64* %test
  br label %while2_start

while2_start:
  %3 = load i64, i64* %test
  %4 = load i64, i64* %curr
  %5 = icmp slt i64 %3, %4
  br i1 %5, label %while2_body, label %while2_end

while2_body:
  %6 = load i64, i64* %test
  %7 = add i64 %6, %p
  store i64 %7, i64* %test

  br label %while2_start
while2_end:
  %8 = load i64, i64* %test
  %9 = load i64, i64* %curr
  %10 = icmp eq i64 %8, %9
  br i1 %10, label %not_prime, label %for_end

not_prime:
  store i64 0, i64* %is_prime
  br label %for_end

for_end:
  %11 = load i64, i64* %i
  %12 = add i64 %11, 1
  store i64 %12, i64* %i
  br label %for_start

for_exit:
  %17 = load i64, i64* %is_prime
  %18 = icmp eq i64 %17, 1
  br i1 %18, label %found_prime, label %next_prime

found_prime:
  %19 = load i64, i64* %found
  %20 = getelementptr %buffer_t, %buffer_t* @buffer, i32 0, i64 %19
  %21 = load i64, i64* %curr
  store i64 %21, i64* %20
  %22 = add i64 %19, 1
  store i64 %22, i64* %found
  br label %next_prime

next_prime:
  %23 = load i64, i64* %curr
  %24 = add i64 %23, 1
  store i64 %24, i64* %curr
  br label %while_start

while_end:
  %26 = sub i64 %n, 1
  %27 = getelementptr %buffer_t, %buffer_t* @buffer, i32 0, i64 %26
  %28 = load i64, i64* %27
  ret i64 %28
}

define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @nth_prime(i64 50)
  ret i64 %1
}