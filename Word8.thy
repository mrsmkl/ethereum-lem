chapter {* Generated by Lem from word8.lem. *}

theory "Word8" 

imports 
 	 Main
	 "Lem_pervasives" 
	 "Lem_word" 

begin 


(*open import Pervasives*)
(*open import Word*)

(*type word8 = W8 of bool * list bool*)

(* perhaps should truncate here? *)
(*val bs_to_w8 : bitSequence -> word8*)
(*let bs_to_w8 seq=  match resizeBitSeq (Just 8) seq with
 | BitSeq _ s b -> W8 s b
end*)

(*val w8_to_bs : word8 -> bitSequence*)
(*let w8_to_bs (W8 s b)=  BitSeq (Just 8) s b*)

(*val word8BinTest : forall 'a. (bitSequence -> bitSequence -> 'a) -> word8 -> word8 -> 'a*)
definition word8BinTest  :: "(bitSequence \<Rightarrow> bitSequence \<Rightarrow> 'a)\<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 'a "  where 
     " word8BinTest binop w1 w2 = ( binop ((\<lambda> w .  bitSeqFromInteger (Some 8) ( (sint w))) w1) ((\<lambda> w .  bitSeqFromInteger (Some 8) ( (sint w))) w2))"


(*val word8BinOp : (bitSequence -> bitSequence -> bitSequence) -> word8 -> word8 -> word8*)
definition word8BinOp  :: "(bitSequence \<Rightarrow> bitSequence \<Rightarrow> bitSequence)\<Rightarrow> 8 word \<Rightarrow> 8 word \<Rightarrow> 8 word "  where 
     " word8BinOp binop w1 w2 = ( (\<lambda> w .  word_of_int (integerFromBitSeq w)) (binop ((\<lambda> w .  bitSeqFromInteger (Some 8) ( (sint w))) w1) ((\<lambda> w .  bitSeqFromInteger (Some 8) ( (sint w))) w2)))"


(*val word8NatOp : (bitSequence -> nat -> bitSequence) -> word8 -> nat -> word8*)
definition word8NatOp  :: "(bitSequence \<Rightarrow> nat \<Rightarrow> bitSequence)\<Rightarrow> 8 word \<Rightarrow> nat \<Rightarrow> 8 word "  where 
     " word8NatOp binop w1 n = ( (\<lambda> w .  word_of_int (integerFromBitSeq w)) (binop ((\<lambda> w .  bitSeqFromInteger (Some 8) ( (sint w))) w1) n))"


(*val word8UnaryOp : (bitSequence -> bitSequence) -> word8 -> word8*)
definition word8UnaryOp  :: "(bitSequence \<Rightarrow> bitSequence)\<Rightarrow> 8 word \<Rightarrow> 8 word "  where 
     " word8UnaryOp op1 w = ( (\<lambda> w .  word_of_int (integerFromBitSeq w)) (op1 ((\<lambda> w .  bitSeqFromInteger (Some 8) ( (sint w))) w)))"


(*val word8ToNat : word8 -> nat*)
(*let word8ToNat w=  natFromInteger (integerFromBitSeq (w8_to_bs w))*)

(*val word8ToInt : word8 -> int*)
(*let word8ToInt w=  intFromInteger (integerFromBitSeq (w8_to_bs w))*)

(*val word8FromInteger : integer -> word8*)
(*let word8FromInteger i=  bs_to_w8 (bitSeqFromInteger (Just 8) i)*)

(*val word8FromInt : int -> word8*)
(*let word8FromInt i=  bs_to_w8 (bitSeqFromInteger (Just 8) (integerFromInt i))*)

(*val word8FromNat : nat -> word8*)
definition word8FromNat  :: " nat \<Rightarrow> 8 word "  where 
     " word8FromNat i = ( (\<lambda> i .  word_of_int ( i)) (int i))"


(*val word8FromBoollist : list bool -> word8*)
(*let word8FromBoollist lst=  match bitSeqFromBoolList lst with
 | Nothing -> bs_to_w8 0
 | Just a -> bs_to_w8 a
end*)

(*val boolListFromWord8 : word8 -> list bool*)
(*let boolListFromWord8 w=  boolListFrombitSeq 8 (w8_to_bs w)*)

(*val word8FromNumeral : numeral -> word8*)
(*let word8FromNumeral w=  bs_to_w8 (Instance_Num_Numeral_Word_bitSequence.fromNumeral w)*)

(*val w8Eq : word8 -> word8 -> bool*)
definition w8Eq  :: " 8 word \<Rightarrow> 8 word \<Rightarrow> bool "  where 
     " w8Eq = ( (op=))"


(*val w8Less : word8 -> word8 -> bool*)
(*let w8Less bs1 bs2=  word8BinTest  
  (Instance_Basic_classes_Ord_Word_bitSequence.<) bs1 bs2*)

(*val w8LessEqual : word8 -> word8 -> bool*)
(*let w8LessEqual bs1 bs2=  word8BinTest  
  (Instance_Basic_classes_Ord_Word_bitSequence.<=) bs1 bs2*)

(*val w8Greater : word8 -> word8 -> bool*)
(*let w8Greater bs1 bs2=  word8BinTest  
  (Instance_Basic_classes_Ord_Word_bitSequence.>) bs1 bs2*)

(*val w8GreaterEqual : word8 -> word8 -> bool*)
(*let w8GreaterEqual bs1 bs2=  word8BinTest  
  (Instance_Basic_classes_Ord_Word_bitSequence.>=) bs1 bs2*)

(*val w8Compare : word8 -> word8 -> ordering*)
(*let w8Compare bs1 bs2=  word8BinTest  
  Instance_Basic_classes_Ord_Word_bitSequence.compare bs1 bs2*)

definition instance_Basic_classes_Ord_Word8_word8_dict  :: "( 8 word)Ord_class "  where 
     " instance_Basic_classes_Ord_Word8_word8_dict = ((|

  compare_method = (genericCompare word_sless w8Eq),

  isLess_method = word_sless,

  isLessEqual_method = word_sle,

  isGreater_method = (\<lambda> x y. word_sless y x),

  isGreaterEqual_method = (\<lambda> x y. word_sle y x)|) )"


(*val word8Negate : word8 -> word8*)
(*let word8Negate=  word8UnaryOp  
  Instance_Num_NumNegate_Word_bitSequence.~*)

(*val word8Succ : word8 -> word8*)
(*let word8Succ=  word8UnaryOp  
  Instance_Num_NumSucc_Word_bitSequence.succ*)

(*val word8Pred : word8 -> word8*)
(*let word8Pred=  word8UnaryOp  
  Instance_Num_NumPred_Word_bitSequence.pred*)

(*val word8Lnot : word8 -> word8*)
(*let word8Lnot=  word8UnaryOp  
  Instance_Word_WordNot_Word_bitSequence.lnot*)

(*val word8Add : word8 -> word8 -> word8*)
(*let word8Add=  word8BinOp  
  (Instance_Num_NumAdd_Word_bitSequence.+)*)

(*val word8Minus : word8 -> word8 -> word8*)
(*let word8Minus=  word8BinOp  
  (Instance_Num_NumMinus_Word_bitSequence.-)*)

(*val word8Mult : word8 -> word8 -> word8*)
(*let word8Mult=  word8BinOp  
  ( Instance_Num_NumMult_Word_bitSequence.* )*)

(*val word8IntegerDivision : word8 -> word8 -> word8*)
(*let word8IntegerDivision=  word8BinOp  
  (Instance_Num_NumDivision_Word_bitSequence./)*)

(*val word8Division : word8 -> word8 -> word8*)
(*let word8Division=  word8BinOp  
  Instance_Num_NumIntegerDivision_Word_bitSequence.div*)

(*val word8Remainder : word8 -> word8 -> word8*)
(*let word8Remainder=  word8BinOp  
  (Instance_Num_NumRemainder_Word_bitSequence.mod)*)

(*val word8Land : word8 -> word8 -> word8*)
(*let word8Land=  word8BinOp  
  (Instance_Word_WordAnd_Word_bitSequence.land)*)

(*val word8Lor : word8 -> word8 -> word8*)
(*let word8Lor=  word8BinOp  
  (Instance_Word_WordOr_Word_bitSequence.lor)*)

(*val word8Lxor : word8 -> word8 -> word8*)
(*let word8Lxor=  word8BinOp  
  (Instance_Word_WordXor_Word_bitSequence.lxor)*)

(*val word8Min : word8 -> word8 -> word8*)
(*let word8Min=  word8BinOp (Instance_Basic_classes_OrdMaxMin_Word_bitSequence.min)*)

(*val word8Max : word8 -> word8 -> word8*)
(*let word8Max=  word8BinOp (Instance_Basic_classes_OrdMaxMin_Word_bitSequence.max)*)

(*val word8Power : word8 -> nat -> word8*)
(*let word8Power=  word8NatOp  
  ( Instance_Num_NumPow_Word_bitSequence.** )*)

(*val word8Asr : word8 -> nat -> word8*)
(*let word8Asr=  word8NatOp  
  (Instance_Word_WordAsr_Word_bitSequence.asr)*)

(*val word8Lsr : word8 -> nat -> word8*)
(*let word8Lsr=  word8NatOp  
  (Instance_Word_WordLsr_Word_bitSequence.lsr)*)

(*val word8Lsl : word8 -> nat -> word8*)
(*let word8Lsl=  word8NatOp  
  (Instance_Word_WordLsl_Word_bitSequence.lsl)*)


definition instance_Num_NumNegate_Word8_word8_dict  :: "( 8 word)NumNegate_class "  where 
     " instance_Num_NumNegate_Word8_word8_dict = ((|

  numNegate_method = (\<lambda> i. - i)|) )"


definition instance_Num_NumAdd_Word8_word8_dict  :: "( 8 word)NumAdd_class "  where 
     " instance_Num_NumAdd_Word8_word8_dict = ((|

  numAdd_method = (op+)|) )"


definition instance_Num_NumMinus_Word8_word8_dict  :: "( 8 word)NumMinus_class "  where 
     " instance_Num_NumMinus_Word8_word8_dict = ((|

  numMinus_method = (op-)|) )"


definition instance_Num_NumSucc_Word8_word8_dict  :: "( 8 word)NumSucc_class "  where 
     " instance_Num_NumSucc_Word8_word8_dict = ((|

  succ_method = (\<lambda> n. n + 1)|) )"


definition instance_Num_NumPred_Word8_word8_dict  :: "( 8 word)NumPred_class "  where 
     " instance_Num_NumPred_Word8_word8_dict = ((|

  pred_method = (\<lambda> n. n - 1)|) )"


definition instance_Num_NumMult_Word8_word8_dict  :: "( 8 word)NumMult_class "  where 
     " instance_Num_NumMult_Word8_word8_dict = ((|

  numMult_method = (op*)|) )"


definition instance_Num_NumPow_Word8_word8_dict  :: "( 8 word)NumPow_class "  where 
     " instance_Num_NumPow_Word8_word8_dict = ((|

  numPow_method = (op^)|) )"


definition instance_Num_NumIntegerDivision_Word8_word8_dict  :: "( 8 word)NumIntegerDivision_class "  where 
     " instance_Num_NumIntegerDivision_Word8_word8_dict = ((|

  div_method = (op div)|) )"


definition instance_Num_NumDivision_Word8_word8_dict  :: "( 8 word)NumDivision_class "  where 
     " instance_Num_NumDivision_Word8_word8_dict = ((|

  numDivision_method = (op div)|) )"


definition instance_Num_NumRemainder_Word8_word8_dict  :: "( 8 word)NumRemainder_class "  where 
     " instance_Num_NumRemainder_Word8_word8_dict = ((|

  mod_method = (op mod)|) )"


definition instance_Basic_classes_OrdMaxMin_Word8_word8_dict  :: "( 8 word)OrdMaxMin_class "  where 
     " instance_Basic_classes_OrdMaxMin_Word8_word8_dict = ((|

  max_method = max,

  min_method = min |) )"


definition instance_Word_WordNot_Word8_word8_dict  :: "( 8 word)WordNot_class "  where 
     " instance_Word_WordNot_Word8_word8_dict = ((|

  lnot_method = (\<lambda> w. (NOT w))|) )"


definition instance_Word_WordAnd_Word8_word8_dict  :: "( 8 word)WordAnd_class "  where 
     " instance_Word_WordAnd_Word8_word8_dict = ((|

  land_method = (op AND)|) )"


definition instance_Word_WordOr_Word8_word8_dict  :: "( 8 word)WordOr_class "  where 
     " instance_Word_WordOr_Word8_word8_dict = ((|

  lor_method = (op OR)|) )"


definition instance_Word_WordXor_Word8_word8_dict  :: "( 8 word)WordXor_class "  where 
     " instance_Word_WordXor_Word8_word8_dict = ((|

  lxor_method = (op XOR)|) )"


definition instance_Word_WordLsl_Word8_word8_dict  :: "( 8 word)WordLsl_class "  where 
     " instance_Word_WordLsl_Word8_word8_dict = ((|

  lsl_method = (op<<)|) )"


definition instance_Word_WordLsr_Word8_word8_dict  :: "( 8 word)WordLsr_class "  where 
     " instance_Word_WordLsr_Word8_word8_dict = ((|

  lsr_method = (op>>)|) )"


definition instance_Word_WordAsr_Word8_word8_dict  :: "( 8 word)WordAsr_class "  where 
     " instance_Word_WordAsr_Word8_word8_dict = ((|

  asr_method = (op>>>)|) )"


end
