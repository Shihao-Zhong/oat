open Assert
open X86
open Ll
open Backend

let tests =
  [ "llprograms/sp18_hw3_petrosky_branches.ll", 0L
  ; "llprograms/sp18_hw3_mannd_quicksort.ll", 1L
  ; "llprograms/sp18_hw3_anon1_bubblesort.ll", 1L
  ; "llprograms/sp18_hw3_geyerj_recursive_gcd.ll", 33L
  ; "llprograms/sp18_hw3_geyerj_call_many_args.ll", 38L
  ; "llprograms/sp18_hw3_kathdix_sumlist.ll", 15L
  ; "llprograms/sp18_hw3_andreasx_selectionsort.ll", 1L
  ; "llprograms/sp18_hw3_xiaov_gep.ll", 6L
  ; "llprograms/sp18_hw3_sakhavan_somilgo_bst_traversal.ll", 1L
  ; "llprograms/sp18_hw3_aen_prime_number.ll", 229L
  ; "llprograms/sp18_hw3_emsu_toposort_dfs.ll", 1L
  ; "llprograms/sp18_hw3_wglisson_mat_multiply.ll", 173L 
  ; "llprograms/sp18_hw3_atter_fib_min_even.ll", 12L
  ]
