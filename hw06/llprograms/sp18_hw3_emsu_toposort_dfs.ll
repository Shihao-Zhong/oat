%arr = type [4 x i64]
%ref = type [1 x i64]
%arrarr = type [4 x %arr]

@graph = global %arrarr [ %arr [i64 0, i64 0, i64 1, i64 1] ,
			  %arr [i64 1, i64 0, i64 1, i64 1] ,
			  %arr [i64 1, i64 1, i64 0, i64 1] ,
			  %arr [i64 1, i64 0, i64 1, i64 0] ]

@seen = global %arr [ i64 0, i64 0, i64 0, i64 0 ]

@topsortidx = global %ref [ i64 0 ]
@toposort = global %arr [i64 0, i64 0, i64 0, i64 0]

define void @dfs_aux(%arrarr* %g, i64 %u, i64 %v) {
	%next = add i64 1, %v
	%cmp = icmp slt i64 %v, 4
	br i1 %cmp, label %check_neighbor, label %finish_loop
check_neighbor:
	%neighbor_ptr = getelementptr %arrarr, %arrarr* @graph, i32 0, i64 %u, i64 %v
	%neighbor_value = load i64, i64* %neighbor_ptr
	%is_neighbor = icmp eq i64 %neighbor_value, 1
	br i1 %is_neighbor, label %check_seen, label %continue
check_seen:
	%seen_idx = getelementptr %arr, %arr* @seen, i32 0, i64 %v
	%seen_value = load i64, i64* %seen_idx
	%not_seen = icmp eq i64 %seen_value, 0
	br i1 %not_seen, label %visit, label %continue
visit:
	call void @dfs(%arrarr* %g, i64 %v)
	call void @dfs_aux(%arrarr* %g, i64 %u, i64 %next)
	ret void
continue:
	call void @dfs_aux(%arrarr* %g, i64 %u, i64 %next)
	ret void
finish_loop:
	ret void
}

define void @dfs(%arrarr* %g, i64 %u) {
	; save node in topological sort
	%idx_ptr = getelementptr %ref, %ref* @topsortidx, i32 0, i32 0
	%idx_val = load i64, i64* %idx_ptr
	%new_idx = add i64 1, %idx_val
	store i64 %new_idx, i64* %idx_ptr
	%toposortidx = getelementptr %arr, %arr* @toposort, i32 0, i64 %idx_val
	store i64 %u, i64* %toposortidx

	; mark seen
	%seen_idx = getelementptr %arr, %arr* @seen, i32 0, i64 %u
	store i64 1, i64* %seen_idx

	; dfs traversal
	call void @dfs_aux(%arrarr* %g, i64 %u, i64 0)
	ret void
}

define i64 @main(i64 %argc, i8** %arcv) {
	call void @dfs(%arrarr* @graph, i64 0)
	%toposortfst = getelementptr %arr, %arr* @toposort, i32 0, i32 0
	%fst = load i64, i64* %toposortfst
	%toposortsnd = getelementptr %arr, %arr* @toposort, i32 0, i32 1
	%snd = load i64, i64* %toposortsnd
	%toposortthird = getelementptr %arr, %arr* @toposort, i32 0, i32 2
	%third = load i64, i64* %toposortthird
	%toposortfourth = getelementptr %arr, %arr* @toposort, i32 0, i32 3
	%fourth = load i64, i64* %toposortfourth
	%fst_check = icmp eq i64 %fst, 0
	%snd_check = icmp eq i64 %snd, 2
	%third_check = icmp eq i64 %third, 1
	%fourth_check = icmp eq i64 %fourth, 3
	%1 = and i1 %fst_check, %snd_check
	%2 = and i1 %third_check, %fourth_check
	%3 = and i1 %1, %2
	br i1 %3, label %success, label %failure
success:
	ret i64 1
failure:
	ret i64 0
}