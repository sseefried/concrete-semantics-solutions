theory Exercise5p2
imports Main
begin

lemma "(\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs) 
     \<or> (\<exists>ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  let ?len_ys = "length xs div 2"
  assume 1: "length xs mod 2 = 0"
  then obtain ys where 2: "ys = take ?len_ys xs" by blast
  then obtain zs where    "zs = drop ?len_ys xs" by blast
  then have "xs = ys @ zs \<and> length ys = length zs" 
    using 1 2 add_diff_cancel_right' append_take_drop_id distrib_right dvd_mult_div_cancel
          even_iff_mod_2_eq_zero length_append length_drop mult.left_neutral one_add_one by auto
  thus ?thesis by blast
next
  let ?len_ys = "length xs div 2 + 1"
  assume 1: "length xs mod 2 \<noteq> 0"
  then obtain ys where 2: "ys = take ?len_ys xs" by blast
  then obtain zs where    "zs = drop ?len_ys xs" by blast
  then have "xs = ys @ zs \<and> length ys = length zs + 1" using 1 2 
    by (smt add.commute add_diff_cancel_left' append_take_drop_id drop_drop even_iff_mod_2_eq_zero
        length_append length_drop mult_2 odd_two_times_div_two_succ)
  thus ?thesis by blast
qed
     
end