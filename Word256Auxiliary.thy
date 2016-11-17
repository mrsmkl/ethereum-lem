chapter {* Generated by Lem from word256.lem. *}

theory "Word256Auxiliary" 

imports 
 	 Main "~~/src/HOL/Library/Code_Target_Numeral"
	 "Lem_pervasives" 
	 "Lem_word" 
	 "Word256" 

begin 


(****************************************************)
(*                                                  *)
(* Lemmata                                          *)
(*                                                  *)
(****************************************************)

lemma bs_to_w256_def_lemma:
" ((\<forall> seq.
   W256 (integerFromBitSeq seq) =
     (\<lambda> w .  word_of_int (integerFromBitSeq w)) seq)) "
(* Theorem: bs_to_w256_def_lemma*)(* try *) by auto

lemma w256_to_bs_def_lemma:
" ((\<forall> i.
   bitSeqFromInteger (Some (( 256 :: nat))) i =
     (\<lambda> w .  bitSeqFromInteger (Some 256) ( (sint w))) (W256 i))) "
(* Theorem: w256_to_bs_def_lemma*)(* try *) by auto

lemma word256ToNat_def_lemma:
" ((\<forall> w.
   nat
     (abs
        (
           (integerFromBitSeq
              ((\<lambda> w .  bitSeqFromInteger (Some 256) ( (sint w))) w))))
     = unat w)) "
(* Theorem: word256ToNat_def_lemma*)(* try *) by auto

lemma word256ToInt_def_lemma:
" ((\<forall> w.
   
     (integerFromBitSeq
        ((\<lambda> w .  bitSeqFromInteger (Some 256) ( (sint w))) w)) =
     sint w)) "
(* Theorem: word256ToInt_def_lemma*)(* try *) by auto

lemma word256FromInteger_def_lemma:
" ((\<forall> i. W256 (i mod base) = (\<lambda> i .  word_of_int ( i)) i)) "
(* Theorem: word256FromInteger_def_lemma*)(* try *) by auto

lemma word256FromInt_def_lemma:
" ((\<forall> i. W256 ( i mod base) = word_of_int i)) "
(* Theorem: word256FromInt_def_lemma*)(* try *) by auto

lemma word256FromBoollist_def_lemma:
" ((\<forall> lst.
   (case  bitSeqFromBoolList lst of
         None => (\<lambda> w .  word_of_int (integerFromBitSeq w))
                   (bitSeqFromInteger None (( 0 :: int)))
     | Some a => (\<lambda> w .  word_of_int (integerFromBitSeq w)) a
   ) = of_bl lst)) "
(* Theorem: word256FromBoollist_def_lemma*)(* try *) by auto

lemma boolListFromWord256_def_lemma:
" ((\<forall> w.
   boolListFrombitSeq (( 256 :: nat))
     ((\<lambda> w .  bitSeqFromInteger (Some 256) ( (sint w))) w) = 
   to_bl w)) "
(* Theorem: boolListFromWord256_def_lemma*)(* try *) by auto

lemma word256FromNumeral_def_lemma:
" ((\<forall> w. W256 (( w :: int) mod base) = ((word_of_int w) :: 256 word))) "
(* Theorem: word256FromNumeral_def_lemma*)(* try *) by auto

lemma w256Less_def_lemma:
" ((\<forall> bs1. \<forall> bs2.
   word256BinTest (op<) bs1 bs2 = word_sless bs1 bs2)) "
(* Theorem: w256Less_def_lemma*)(* try *) by auto

lemma w256LessEqual_def_lemma:
" ((\<forall> bs1. \<forall> bs2.
   word256BinTest (op \<le>) bs1 bs2 = word_sle bs1 bs2)) "
(* Theorem: w256LessEqual_def_lemma*)(* try *) by auto

lemma w256Greater_def_lemma:
" ((\<forall> bs1. \<forall> bs2.
   word256BinTest (op>) bs1 bs2 = word_sless bs2 bs1)) "
(* Theorem: w256Greater_def_lemma*)(* try *) by auto

lemma w256GreaterEqual_def_lemma:
" ((\<forall> bs1. \<forall> bs2.
   word256BinTest (op \<ge>) bs1 bs2 = word_sle bs2 bs1)) "
(* Theorem: w256GreaterEqual_def_lemma*)(* try *) by auto

lemma w256Compare_def_lemma:
" ((\<forall> bs1. \<forall> bs2.
   word256BinTest (genericCompare (op<) (op=)) bs1 bs2 =
     (genericCompare word_sless w256Eq bs1 bs2))) "
(* Theorem: w256Compare_def_lemma*)(* try *) by auto

lemma word256Negate_def_lemma:
" (( word256UnaryOp (\<lambda> i. - i) = (\<lambda> i. - i))) "
(* Theorem: word256Negate_def_lemma*)(* try *) by auto

lemma word256Succ_def_lemma:
" (( word256UnaryOp (\<lambda> n. n + ( 1 :: int)) = (\<lambda> n. n + 1))) "
(* Theorem: word256Succ_def_lemma*)(* try *) by auto

lemma word256Pred_def_lemma:
" (( word256UnaryOp (\<lambda> n. n - ( 1 :: int)) = (\<lambda> n. n - 1))) "
(* Theorem: word256Pred_def_lemma*)(* try *) by auto

lemma word256Lnot_def_lemma:
" (( word256UnaryOp integerLnot = (\<lambda> w. (NOT w)))) "
(* Theorem: word256Lnot_def_lemma*)(* try *) by auto

lemma word256Add_def_lemma:
" (( word256BinOp (op+) = (op+))) "
(* Theorem: word256Add_def_lemma*)(* try *) by auto

lemma word256Minus_def_lemma:
" (( word256BinOp (op-) = (op-))) "
(* Theorem: word256Minus_def_lemma*)(* try *) by auto

lemma word256Mult_def_lemma:
" (( word256BinOp (op*) = (op*))) "
(* Theorem: word256Mult_def_lemma*)(* try *) by auto

lemma word256IntegerDivision_def_lemma:
" (( word256BinOp (op div) = (op div))) "
(* Theorem: word256IntegerDivision_def_lemma*)(* try *) by auto

lemma word256Division_def_lemma:
" (( word256BinOp (op div) = (op div))) "
(* Theorem: word256Division_def_lemma*)(* try *) by auto

lemma word256Remainder_def_lemma:
" (( word256BinOp (op mod) = (op mod))) "
(* Theorem: word256Remainder_def_lemma*)(* try *) by auto

lemma word256Land_def_lemma:
" (( word256BinOp integerLand = (op AND))) "
(* Theorem: word256Land_def_lemma*)(* try *) by auto

lemma word256Lor_def_lemma:
" (( word256BinOp integerLor = (op OR))) "
(* Theorem: word256Lor_def_lemma*)(* try *) by auto

lemma word256Lxor_def_lemma:
" (( word256BinOp integerLxor = (op XOR))) "
(* Theorem: word256Lxor_def_lemma*)(* try *) by auto

lemma word256Min_def_lemma:
" (( word256BinOp (min) = min)) "
(* Theorem: word256Min_def_lemma*)(* try *) by auto

lemma word256Max_def_lemma:
" (( word256BinOp (max) = max)) "
(* Theorem: word256Max_def_lemma*)(* try *) by auto

lemma word256Power_def_lemma:
" (( word256NatOp (op^) = (op^))) "
(* Theorem: word256Power_def_lemma*)(* try *) by auto

lemma word256Asr_def_lemma:
" (( word256NatOp integerAsr = (op>>>))) "
(* Theorem: word256Asr_def_lemma*)(* try *) by auto

lemma word256Lsr_def_lemma:
" (( word256NatOp integerAsr = (op>>))) "
(* Theorem: word256Lsr_def_lemma*)(* try *) by auto

lemma word256Lsl_def_lemma:
" (( word256NatOp integerLsl = (op<<))) "
(* Theorem: word256Lsl_def_lemma*)(* try *) by auto

lemma word256UGT_def_lemma:
" ((\<forall> a. \<forall> b. (unat a > unat b) = a > b)) "
(* Theorem: word256UGT_def_lemma*)(* try *) by auto



end
