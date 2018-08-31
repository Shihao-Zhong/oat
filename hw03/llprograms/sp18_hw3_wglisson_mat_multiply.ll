%vec4 = type [4 x i64]
%mat4 = type [4 x %vec4]

@matrix1 = global %mat4 [
    %vec4 [i64 12, i64 0, i64 3, i64 2],
    %vec4 [i64 20, i64 7, i64 8, i64 15],
    %vec4 [i64 3,  i64 6, i64 5, i64 12],
    %vec4 [i64 10, i64 2, i64 9, i64 5]
]

@matrix2 = global %mat4 [
    %vec4 [i64 12, i64 0, i64 3, i64 2],
    %vec4 [i64 20, i64 7, i64 8, i64 15],
    %vec4 [i64 3,  i64 6, i64 5, i64 12],
    %vec4 [i64 10, i64 2, i64 9, i64 5]
]

@row_val = global i64 0;
@col_val = global i64 0;
@n = global i64 4

define i64 @get_row_val (%mat4* %matrix, i64 %row, i64 %off) {
    %ptr = getelementptr %mat4, %mat4* %matrix, i32 0, i64 %row, i64 %off
    %val = load i64, i64* %ptr
    ret i64 %val 
}

define i64 @get_col_val (%mat4* %matrix, i64 %col, i64 %off) {
    %ptr = getelementptr %mat4, %mat4* %matrix, i32 0, i64 %off, i64 %col
    %val = load i64, i64* %ptr
    ret i64 %val 
}

define i64 @multiply (%mat4* %mat_1, %mat4* %mat_2, i64 %i, i64 %j, i64 %off) {
    %i_val = call i64 @get_row_val (%mat4* %mat_1, i64 %i, i64 %off)
    %j_val = call i64 @get_col_val (%mat4* %mat_2, i64 %j, i64 %off)
    %prod = mul i64 %i_val, %j_val
    ret i64 %prod
}

define i64 @sum_products (%mat4* %mat_1, %mat4* %mat_2, i64 %i, i64 %j) {
    %sum = alloca i64
    store i64 0, i64* %sum
    %offset = alloca i64
    store i64 0, i64* %offset
    br label %cond

cond:
    %1 = load i64, i64* %offset
    %n = load i64, i64* @n
    %2 = icmp slt i64 %1, %n
    br i1 %2, label %loop, label %loop_exit

loop:
    %off = load i64, i64* %offset
    %3 = call i64 @multiply (%mat4* %mat_1, %mat4* %mat_2, i64 %i, i64 %j, i64 %off)
    %4 = load i64, i64* %sum
    %5 = add i64 %3, %4
    store i64 %5, i64* %sum
    br label %inc

inc:
    %6 = load i64, i64* %offset
    %7 = add i64 1, %6
    store i64 %7, i64* %offset
    br label %cond

loop_exit:
    %8 = load i64, i64* %sum
    ret i64 %8
}

define i64 @main(i64 %argc, i8** %arcv) {
    %i = load i64, i64* @row_val
    %j = load i64, i64* @col_val
    %1 = call i64 @sum_products (%mat4* @matrix1, %mat4* @matrix2, i64 %i, i64 %j)
    ret i64 %1
}