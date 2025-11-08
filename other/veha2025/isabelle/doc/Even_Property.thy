theory Even_Property imports Main begin

	\<comment> \<open>Примитивно-рекурсивная функция, устанавливающая, что заданное целое число чётно.\<close>
primrec is_even :: \<open>nat \<Rightarrow> bool\<close> where
	\<comment> \<open>Задание 1.\<close>
	even_Zero:	\<open>is_even 0	\<longleftrightarrow> True\<close>
|	even_Suc:	\<open>is_even (Suc n)	\<longleftrightarrow> True\<close>

	\<comment> \<open>Целое или следующее за ним число нечётно.\<close>
lemma successive_is_even: \<open>is_even n \<or> is_even (Suc n)\<close>
	\<comment> \<open>Задание 2.\<close>
oops

	\<comment> \<open>Целое или следующее за ним число чётно.\<close>
lemma successive_exclusive_is_even: \<open>is_even n \<noteq> is_even (Suc n)\<close>
	\<comment> \<open>Задание 3.\<close>
oops

lemma is_even_mult: \<open>is_even (x * y) \<longleftrightarrow> is_even x \<or> is_even y\<close>
	\<comment> \<open>Задание 4.\<close>
oops

lemma is_odd_foldr:
	\<open>\<not> is_even (foldr (*) xs y) \<Longrightarrow> z \<in> set xs \<Longrightarrow> \<not> is_even z\<close>
	\<comment> \<open>Задание 5.\<close>
oops

lemma is_odd_filter:
	\<open>\<not> is_even (foldr (*) (filter P xs) y) \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x \<Longrightarrow>
	\<not> is_even x\<close>
	\<comment> \<open>Задание 6.\<close>
oops

lemma odd_expr_even_mult: \<open>\<not> is_even ((x + y) * z) \<Longrightarrow> is_even (x * y)\<close>
	\<comment> \<open>Задание 7.\<close>
oops

end