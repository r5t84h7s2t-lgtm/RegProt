theory Word_Utils
  imports
    Main
    "HOL-Library.Word"
begin

section \<open>Register Bit Operation\<close>

abbreviation bit_left_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix "<<" 50)
where "x << n \<equiv> push_bit n x"

abbreviation bit_right_shift ::
  "'a :: len word \<Rightarrow> nat \<Rightarrow> 'a :: len word" (infix ">>" 50)
  where "x >> n \<equiv> drop_bit n x"

definition set_reg_bit :: 
  "64 word \<Rightarrow> nat \<Rightarrow> 64 word"
  where
    "set_reg_bit r n \<equiv> set_bit n r"

definition unset_reg_bit ::
  "64 word \<Rightarrow> nat \<Rightarrow> 64 word"
  where
    "unset_reg_bit r n \<equiv> unset_bit n r"

definition get_reg_bit ::
  "64 word \<Rightarrow> nat \<Rightarrow> bool"
  where
    "get_reg_bit r n \<equiv>
      let
        r' = set_reg_bit r n
      in
        r' = r"

section \<open> Register Structure to 64-bit Word Conversion \<close>

fun bool_to_word64 :: "bool \<Rightarrow> 64 word" where
  "bool_to_word64 True = 1"
| "bool_to_word64 False = 0"

fun or_list :: "64 word list \<Rightarrow> 64 word" where
  "or_list [] = 0" |
  "or_list (x # xs) = or x (or_list xs)"

definition test_bit :: "('a::len) word \<Rightarrow> nat \<Rightarrow> bool" where
  "test_bit word n \<equiv> and (word >> n) 1 \<noteq> 0"

end
