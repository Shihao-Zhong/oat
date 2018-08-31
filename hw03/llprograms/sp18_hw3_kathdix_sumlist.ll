%node = type {i64, %node*}

@head = global %node {i64 1, %node* @next1}
@next1 = global %node {i64 -2, %node* @next2}
@next2 = global %node {i64 10, %node* @next3}
@next3 = global %node {i64 6, %node* @next4}
@next4 = global %node {i64 -6, %node* @next5}
@next5 = global %node {i64 2, %node* @tail}
@tail = global %node {i64 4, %node* null}

define i64 @sumList() {
  %count = alloca i64
  store i64 0, i64* %count
  %sum = alloca i64
  store i64 0, i64* %sum
  %ptr = alloca i64*
  %ptrN = getelementptr %node, %node* @head, i32 0, i32 0
  store i64* %ptrN, i64** %ptr
  br label %loop2
loop2:
  %currnode = load i64*, i64** %ptr
  %val = load i64, i64* %currnode	
  %currSum = load i64, i64* %sum
  %newSum = add i64 %val, %currSum
  store i64 %newSum, i64* %sum
  %tmp = load i64, i64* %count
  %tmp2 = add i64 %tmp, 1
  store i64 %tmp2, i64* %count
  %cmp = icmp eq i64 %tmp2, 7
  br i1 %cmp, label %end2, label %update_pointer
update_pointer:
  %currptr = load i64*, i64** %ptr
  %tempptr = bitcast i64* %currptr to %node*
  %link = getelementptr %node, %node* %tempptr, i32 0, i32 1 
  %newptr = load %node*, %node** %link
  %castedptr = bitcast %node* %newptr to i64*
  store i64* %castedptr, i64** %ptr
  br label %loop2
end2:
  %returnVal = load i64, i64* %sum
  ret i64 %returnVal
}


define i64 @main(i64 %argc, i8** %arcv) {
  %1 = call i64 @sumList()
  ret i64 %1
}