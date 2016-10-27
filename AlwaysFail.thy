theory AlwaysFail

imports Main "./Evm" "./RelationalSem"

begin

definition this_address :: address
where "this_address = undefined"

abbreviation always_fail_code :: "inst list"
where
"always_fail_code ==
   Stack (PUSH_N [0])
 # Annotation (\<lambda> aenv. aenv_stack aenv ! 0 = 0)
 # Pc JUMP #
 []"


value "program_of_lst always_fail_code"
value "program_content_of_lst 0 always_fail_code 3"

abbreviation always_fail_account_state :: "uint \<Rightarrow> account_state"
where
"always_fail_account_state balance ==
   \<lparr> account_address = this_address
   , account_storage = \<lambda> _. 0
   , account_code = program_of_lst (always_fail_code)
   , account_balance = balance
   , account_ongoing_calls = []
   , account_killed = False
   \<rparr>"

abbreviation always_fail_spec :: "uint \<Rightarrow> response_to_world"
where
" always_fail_spec initial_balance ==
  \<lparr> when_called = \<lambda> _. (ContractFail,
                        \<lambda> a. a = always_fail_account_state initial_balance)
  , when_returned = \<lambda> _. (ContractFail, 
                           \<lambda> a. a = always_fail_account_state initial_balance)
  , when_failed = (ContractFail,
                     \<lambda> a. a = always_fail_account_state initial_balance)
  \<rparr>
"

declare eval_annotation_def [simp]

(*
lemma problem :
"node \<langle> x, ll, elm, rr\<rangle> y \<langle>\<rangle> = Node (x + 1) \<langle> x, ll, elm, rr\<rangle> y \<langle>\<rangle> "
apply(simp add: node_def)
done

lemma problem2 :
"node \<langle>\<rangle> y \<langle>x, \<langle>\<rangle>, elm, \<langle>\<rangle>\<rangle> = Node (x + 1) \<langle>\<rangle> y \<langle> x, \<langle>\<rangle>, elm, \<langle>\<rangle>\<rangle>"
apply(simp add: node_def)
done
*)

lemma update_account_state_None [simp] :
"update_account_state prev act st bal None =
   (prev \<lparr>
     account_storage := st,
     account_balance := (case act of ContractFail \<Rightarrow> account_balance prev
                                   |  _ \<Rightarrow> bal (account_address prev)),
     account_ongoing_calls := account_ongoing_calls prev,
     account_killed :=
       (case act of ContractSuicide \<Rightarrow> True
                  | _ \<Rightarrow> account_killed prev)
   \<rparr>)"
apply(case_tac act; simp add: update_account_state_def)
done

lemma update_account_state_Some [simp] :
"update_account_state prev act st bal (Some pushed) =
   (prev \<lparr>
     account_storage := st,
     account_balance := (case act of ContractFail \<Rightarrow> account_balance prev
                                   |  _ \<Rightarrow> bal (account_address prev)),
     account_ongoing_calls := pushed # account_ongoing_calls prev,
     account_killed := (case act of ContractSuicide \<Rightarrow> True
                  | _ \<Rightarrow> account_killed prev)
  \<rparr>)"
apply(case_tac act; simp add: update_account_state_def)
done

declare respond_to_call_correctly_def [simp]
declare respond_to_return_correctly_def [simp]
declare respond_to_fail_correctly_def [simp]
declare build_cenv_def [simp]
declare program_of_lst_def [simp]
declare build_venv_called.simps [simp]

declare program_sem.psimps [simp]

text {* The following lemma is just for controlling the Isabelle/HOL simplifier. *}

value "program_content_of_lst 0 always_fail_code"

lemma unblock_program_sem [simp] : "blocked_program_sem v c l p True = program_sem v c l p"
apply(simp add: blocked_program_sem.psimps)
done

lemma program_sem_unblock :
"program_sem_blocked v c internal external True = program_sem v c internal external"
apply(simp add: program_sem_blocked_def)
done


declare one_round.simps [simp]
declare world_turn.simps [simp]
declare contract_turn.simps [simp]

(*
declare program_annotation_of_lst_def [simp]
*)
declare program_sem.simps [simp]

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

declare venv_advance_pc_def [simp]
declare build_aenv_def [simp]
declare jump_def [simp]
declare word_of_bytes_def [simp]
declare instruction_failure_result_def [simp]
declare build_venv_returned.simps [simp]
declare build_venv_failed_def [simp]

lemma always_fail_correct:
"
  account_state_responds_to_world
  (\<lambda> a. a = always_fail_account_state initial_balance)
  (always_fail_spec initial_balance)
"
apply(rule AccountStep; auto)
apply(case_tac steps; auto)
done

lemma no_assertion_failure:
"no_assertion_failure (\<lambda> a. \<exists> initial_balance. a = (always_fail_account_state initial_balance))"
apply(simp add: no_assertion_failure_def)
apply(auto)
 apply(drule star_case; auto simp add: no_assertion_failure_post_def)
 apply(case_tac steps; auto)
 apply(drule star_case; auto)
apply(case_tac steps; auto)
done

lemma balance_no_decrease:
"
pre_post_conditions (\<lambda> a. \<exists> initial_balance. a = (always_fail_account_state initial_balance))
(\<lambda> initial_state init_call. True)
(\<lambda> initial_state _ (post_state, _). account_balance initial_state \<le> account_balance post_state)
"
apply(simp add: pre_post_conditions_def; auto)
         apply(drule star_case; auto)
        apply(case_tac steps; auto)
        apply(case_tac steps; auto)
       apply(drule star_case; auto)
       apply(case_tac steps; auto)
      apply(drule star_case; auto)
      apply(case_tac steps; auto)
     apply(drule star_case; auto)
     apply(case_tac steps; auto)
    apply(drule star_case; auto)
    apply(case_tac steps; auto)
   apply(drule star_case; auto)
   apply(case_tac steps; auto)
  apply(drule star_case; auto)
  apply(case_tac steps; auto)
 apply(drule star_case; auto)
 apply(case_tac steps; auto)
 apply(drule star_case; auto)
apply(case_tac steps; auto)
done

end
