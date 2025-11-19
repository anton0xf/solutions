theory Task imports Main begin


subsection \<open>Part I\<close>

\<comment> \<open>If @{term foldr} over conjuctions evaluates to @{term True}, the initial value is @{term True}.\<close>
lemma foldr_conj_init: \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
proof (induction xs)
  case Nil 
  then show \<open>foldr (\<lambda> x b. P x \<and> b) [] y \<Longrightarrow> y\<close> by simp
next
  case (Cons x xs)
  assume \<open>foldr (\<lambda> x b. P x \<and> b) xs y \<Longrightarrow> y\<close>
	then show \<open>foldr (\<lambda> x b. P x \<and> b) (x # xs) y \<Longrightarrow> y\<close> by simp
qed

\<comment> \<open>@{term foldr} over conjuctions with initial value @{term True} evaluates to @{term True} if an only if all conjuncts are @{term True}.\<close>
lemma foldr_conj_prop:
	\<open>foldr (\<lambda> x b. P x \<and> b) xs True \<longleftrightarrow> (\<forall> x \<in> set xs. P x)\<close>
proof (induction xs)
  case Nil
  then show \<open>foldr (\<lambda> x b. P x \<and> b) [] True \<longleftrightarrow> (\<forall> x \<in> set []. P x)\<close> by simp
next
  case (Cons y ys)
  assume \<open>foldr (\<lambda> x b. P x \<and> b) ys True \<longleftrightarrow> (\<forall> x \<in> set ys. P x)\<close>
  then show \<open>foldr (\<lambda> x b. P x \<and> b) (y # ys) True \<longleftrightarrow> (\<forall> x \<in> set (y # ys). P x)\<close> by simp
qed

subsection \<open>Part II\<close>

\<comment> \<open>Pick the given number of first elements of the given list.
The function uses recursion on the number of elements to pick.\<close>
primrec pick :: \<open>nat \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
	\<open>pick 0 xs = []\<close> |
	\<open>pick (Suc n) xs = (case xs of [] \<Rightarrow> [] | x # xs \<Rightarrow> x # pick n xs)\<close>

\<comment> \<open>The length of the prefix is the minimum between the specified prefix length and the original list length.\<close>
lemma pick_length: \<open>length (pick n xs) = min n (length xs)\<close>
proof (induction n)
  case 0
  then show \<open>length (pick 0 xs) = min 0 (length xs)\<close> by simp
next
  case (Suc n)
  assume \<open>length (pick n xs) = min n (length xs)\<close>
  then show \<open>length (pick (Suc n) xs) = min (Suc n) (length xs)\<close>
  proof (induction xs)
    case Nil
    then show \<open>length (pick (Suc n) []) = min (Suc n) (length [])\<close> by simp
  next
    case (Cons y ys)
    assume \<open>length (pick (Suc n) ys) = min (Suc n) (length ys)\<close>
    then have \<open>min (Suc n) (length (y # ys)) = min n (length ys)\<close> by simp
    then show \<open>length (pick (Suc n) (y # ys)) = min (Suc n) (length (y # ys))\<close> by simp
  qed
qed

\<comment> \<open>The elements of the prefix obtained with @{term pick} are the first elements of the original list.\<close>
lemma pick_items: \<open>\<forall> i < length (pick n xs). (pick n xs) ! i = xs ! i\<close>
	sorry

\<comment> \<open>Function @{term pick} is equivalent to function @{term take}.\<close>
lemma pick_take_eq: \<open>pick n xs = take n xs\<close>
	by (simp add: list_eq_iff_nth_eq pick_items pick_length)


subsection \<open>Part III\<close>

\<comment> \<open>The function precedes every list in the second argument (which is a list of lists) with the corresponding item from the first argument. The lists that have no corresponding pair are replaced with an empty list.\<close>
primrec conss :: "'a list \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
	conss_Nil:	"conss xs [] = []" |
	conss_Cons:	"conss xs (y # ys) =
			(case xs of [] \<Rightarrow> [] | z # zs \<Rightarrow> (z # y) # conss zs ys)"

\<comment> \<open>The following tests demonstrate how the function @{term conss} is expected to work.\<close>
lemma conss_test_1: \<open>conss [1] [] = []\<close> by simp
lemma conss_test_2: \<open>conss [1, 2] [] = []\<close> by simp
lemma conss_test_3: \<open>conss [] [[1]] = []\<close> by simp
lemma conss_test_4: \<open>conss [] [[1, 2]] = []\<close> by simp
lemma conss_test_5: \<open>conss [1] [[2]] = [[1, 2]]\<close> by simp
lemma conss_test_6: \<open>conss [1, 2] [[3], [4]] = [[1, 3], [2, 4]]\<close> by simp
lemma conss_test_7: \<open>conss [1, 2] [[3]] = [[1, 3]]\<close> by simp
lemma conss_test_8: \<open>conss [1] [[2], [3]] = [[1, 2]]\<close> by simp

\<comment> \<open>The length of @{term \<open>conss xs ys\<close>} is the minimum length of @{term xs} and @{term ys}.\<close>
lemma conss_length: \<open>length (conss xs ys) = min (length xs) (length ys)\<close>
	sorry

\<comment> \<open>The result of @{term conss}, applied to non-empty lists, is a @{term Cons} of the lists heads with a @{term conss}, applied to the lists tails.\<close>
lemma conss_Cons_Cons: \<open>conss (x # xs) (y # ys) = (x # y) # conss xs ys\<close>
	sorry

\<comment> \<open>If all lists in the list of lists are non-empty, it can be obtained by applying @{term conss} to the maps of heads and tails.\<close>
lemma hd_conss_tl:
	\<open>\<forall> x \<in> set xs. x \<noteq> [] \<Longrightarrow> conss (map hd xs) (map tl xs) = xs\<close>
	sorry

\<comment> \<open>If a list is obtained from a list of lists @{term s} by filtering all non-empty nested lists with a given property @{term P}, then applying @{term conss} to the heads and tails of the list, gives this list.\<close>
lemma hd_conss_tl_filter:
	\<open>conss
		(map hd (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
		(map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s))
	= filter (\<lambda>xs. xs \<noteq> [] \<and> P xs) s\<close>
	sorry

lemma tl_ne: \<open>xs \<noteq> [] \<Longrightarrow> hd xs # ys \<noteq> xs \<Longrightarrow> tl xs \<noteq> ys\<close>
	sorry

\<comment> \<open>A non-empty list with head @{term x} and tail @{term xs} is in the list of lists @{term s} if and only if @{term xs} is in the tails of the lists from @{term s} that have @{term x} as their head.\<close>
lemma tl_filter_hd: \<open>x # xs \<in> set s \<longleftrightarrow>
			xs \<in> set (map tl (filter (\<lambda>xs. xs \<noteq> [] \<and> hd xs = x) s))\<close>
	sorry

end