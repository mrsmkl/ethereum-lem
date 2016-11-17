chapter {* Generated by Lem from compile.lem. *}

theory "CompileAuxiliary" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "Lem_pervasives" 
	 "Evm" 
	 "Word8" 
	 "Rlp" 
	 "Compile" 

begin 


(****************************************************)
(*                                                  *)
(* Termination Proofs                               *)
(*                                                  *)
(****************************************************)

(*
termination big_step by lexicographic_order
*)

termination get_expr by lexicographic_order

termination compile_expr by lexicographic_order


(****************************************************)
(*                                                  *)
(* Lemmata                                          *)
(*                                                  *)
(****************************************************)

declare respond_to_call_correctly_def [simp]
declare respond_to_return_correctly_def [simp]
declare respond_to_fail_correctly_def [simp]
declare build_cenv_def [simp]
declare program_of_lst_def [simp]
declare build_venv_called.simps [simp]
declare eval_annotation_def [simp]
declare program_sem.psimps [simp]
declare program_sem.simps [simp]

text {* The following lemma is just for controlling the Isabelle/HOL simplifier. *}

value "program_content_of_lst 0 always_fail_code"

lemma unblock_program_sem [simp] : "blocked_program_sem v c l p True = program_sem v c l p"
apply(simp add: blocked_program_sem.psimps)
done

lemma program_sem_unblock :
"program_sem_blocked v c internal external True = program_sem v c internal external"
apply(simp add: program_sem_blocked_def)
done



(*
declare program_annotation_of_lst_def [simp]
*)

lemma strict_if_True [simp] :
"strict_if True a b = a True"
apply(simp add: strict_if_def)
done

text {* When the if-condition is known to be False, the simplifier
can proceed into the else-clause. *}

lemma strict_if_False [simp] :
"strict_if False a b = b True"
apply(simp add: strict_if_def)
done

text {* When the if-condition is not known to be either True or False,
the simplifier is allowed to perform computation on the if-condition. *}

lemma strict_if_cong [cong] :
"b0 = b1 \<Longrightarrow> strict_if b0 x y = strict_if b1 x y"
apply(auto)
done

(*
declare store_byte_list_in_program.simps [simp]
*)

lemma foo  [cong] : "100 = Suc 99"
apply(auto)
done

declare check_annotations_def [simp]

declare program_content_of_lst.simps [simp]
declare store_byte_list_in_program.simps [simp]
declare program_annotation_of_lst.simps [simp]
declare prepend_annotation_def [simp]
declare inst_size_def [simp]
declare inst_code.simps [simp]
declare stack_inst_code.simps [simp]
declare venv_next_instruction_def [simp]
declare instruction_sem.simps [simp]
declare stack_0_1_op_def [simp]
declare venv_advance_pc_def [simp]
declare build_aenv_def [simp]
declare jump_def [simp]
(* declare word_of_bytes_def [simp] *)
declare instruction_failure_result_def [simp]
declare build_venv_returned.simps [simp]
declare build_venv_failed_def [simp]
declare compile_simple.simps [simp]
declare get_simple.simps [simp]
declare get_stack_top.simps [simp]

declare eval_expr_def [simp]

(*
value "size (0::256 word)"

definition zurp :: "256 word \<Rightarrow> 256 word" where
"zurp k = k"

theorem foo3 [simp] : "size (w::256 word) = 256"
apply (auto simp:word_size)
done
*)

theorem foo2 : "length ((word_rsplit (w::256 word)) :: 8 word list) = 32"
apply(rule length_word_rsplit_even_size)
apply(auto simp:word_size)
done

theorem list_elems : "length lst = Suc x \<Longrightarrow>
 \<exists>b1 tl. lst = Cons b1 tl"
apply(induction lst)
apply(auto)
done

theorem list_elems1 : "length lst = 1 \<Longrightarrow> \<exists>b1. lst = [b1]"
apply(rule exE)
apply(rule list_elems)
apply(auto)
done

theorem list_elems2 : "length lst = 2 \<Longrightarrow> \<exists>b1 b2. lst = [b1,b2]"
apply(insert list_elems [of lst 1])
apply(auto)
apply(rule exE)
apply(rule list_elems)
apply(auto)
done

theorem list_elems3 : "length lst = 3 \<Longrightarrow> \<exists>b1 b2 b3. lst = [b1,b2,b3]"
apply(insert list_elems [of lst 2])
apply(auto)
apply(insert list_elems [of "drop 1 lst" 1])
apply(auto)
apply(insert list_elems [of "drop 2 lst" 0])
apply(auto)
done

theorem list_elems32 : "length lst = 32 \<Longrightarrow>
 \<exists>b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32.
 lst = [b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,
b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,
b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32]"

apply(insert list_elems [of lst 31])
apply(auto)
apply(insert list_elems [of "drop 1 lst" 30])
apply(auto)
apply(insert list_elems [of "drop 2 lst" 29])
apply(auto)
apply(insert list_elems [of "drop 3 lst" 28])
apply(auto)
apply(insert list_elems [of "drop 4 lst" 27])
apply(auto)
apply(insert list_elems [of "drop 5 lst" 26])
apply(auto)
apply(insert list_elems [of "drop 6 lst" 25])
apply(auto)
apply(insert list_elems [of "drop 7 lst" 24])
apply(auto)
apply(insert list_elems [of "drop 8 lst" 23])
apply(auto)
apply(insert list_elems [of "drop 9 lst" 22])
apply(auto)
apply(insert list_elems [of "drop 10 lst" 21])
apply(auto)
apply(insert list_elems [of "drop 11 lst" 20])
apply(auto)
apply(insert list_elems [of "drop 12 lst" 19])
apply(auto)
apply(insert list_elems [of "drop 13 lst" 18])
apply(auto)
apply(insert list_elems [of "drop 14 lst" 17])
apply(auto)
apply(insert list_elems [of "drop 15 lst" 16])
apply(auto)
apply(insert list_elems [of "drop 16 lst" 15])
apply(auto)
apply(insert list_elems [of "drop 17 lst" 14])
apply(auto)
apply(insert list_elems [of "drop 18 lst" 13])
apply(auto)
apply(insert list_elems [of "drop 19 lst" 12])
apply(auto)
apply(insert list_elems [of "drop 20 lst" 11])
apply(auto)
apply(insert list_elems [of "drop 21 lst" 10])
apply(auto)
apply(insert list_elems [of "drop 22 lst" 9])
apply(auto)
apply(insert list_elems [of "drop 23 lst" 8])
apply(auto)
apply(insert list_elems [of "drop 24 lst" 7])
apply(auto)
apply(insert list_elems [of "drop 25 lst" 6])
apply(auto)
apply(insert list_elems [of "drop 26 lst" 5])
apply(auto)
apply(insert list_elems [of "drop 27 lst" 4])
apply(auto)
apply(insert list_elems [of "drop 28 lst" 3])
apply(auto)
apply(insert list_elems [of "drop 29 lst" 2])
apply(auto)
apply(insert list_elems [of "drop 30 lst" 1])
apply(auto)
apply(insert list_elems [of "drop 31 lst" 0])
apply(auto)
done

theorem word_elems32 : "\<exists>b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
b11 b12 b13 b14 b15 b16 b17 b18 b19 b20
b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31 b32.
 (word_rsplit (w::256 word) :: 8 word list) =
 [b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,
b11,b12,b13,b14,b15,b16,b17,b18,b19,b20,
b21,b22,b23,b24,b25,b26,b27,b28,b29,b30,b31,b32]"
apply(rule list_elems32)
apply(rule foo2)
done

fun get_foo :: "simple \<Rightarrow> 256 word" where
  "get_foo (Compile.ImmedV x) = x"
| "get_foo (Compile.MemoryV x) = x"
| "get_foo (Compile.StorageV x) = x"

declare stop_def [simp]
declare mload_def [simp]
declare general_dup_def [simp]
declare stack_1_1_op_def [simp]

theorem simple_correct :
"( eval_expr v addr (compile_simple expr) = get_simple v expr)"
(* Theorem: simple_correct*)(* try *)
apply(insert word_elems32 [of "get_foo expr"])
apply(induction expr)
apply(auto)
apply(subst foo)
apply(subst foo)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(subst foo)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply (metis word_rcat_rsplit)

apply(subst foo)
apply(subst foo)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(subst foo)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(subst foo)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply (metis word_rcat_rsplit)

apply(subst foo)
apply(subst foo)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(subst foo)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(subst foo)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply (metis word_rcat_rsplit)
done

(*
apply(subst foo)
apply(subst foo)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(case_tac "index (venv_stack v) (unat x - Suc 0)")
apply(auto)
*)

(*
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(subst program_sem.simps)
apply(auto simp:foo2)
apply(auto)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(subst word_rsplit_def)
apply(auto)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_aux.simps)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
apply(subst bin_rsplit_def)
*)

theorem expr_correct :
"( \<forall> expr.  \<forall> v.  \<forall> addr.  eval_expr v addr (compile_expr expr) = get_expr v expr)"
(* Theorem: expr_correct*)(* try *) by auto



end