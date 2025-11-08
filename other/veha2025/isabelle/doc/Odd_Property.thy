theory Odd_Property imports Main begin

	\<comment> \<open>Примитивно-рекурсивная функция, устанавливающая, что заданное целое число нечётно.\<close>
primrec is_odd :: \<open>nat \<Rightarrow> bool\<close> where
	odd_Zero:	\<open>is_odd 0	\<longleftrightarrow> False\<close>	\<comment> \<open>Ноль, базовый случай.\<close>
|	odd_Suc:	\<open>is_odd (Suc n)	\<longleftrightarrow> \<not> is_odd n\<close>	\<comment> \<open>Число, следующее за @{term n}.\<close>

	\<comment> \<open>Целое или следующее за ним число нечётно.\<close>
lemma successive_is_odd: \<open>is_odd n \<or> is_odd (Suc n)\<close>
	\<comment> \<open>Доказательство по индукции.\<close>
proof (induction n)
		\<comment> \<open>Базовый случай.\<close>
	case 0
		\<comment> \<open>Единица @{term \<open>Suc 0\<close>} нечётная.\<close>
	have \<open>is_odd (Suc 0)\<close> using odd_Zero odd_Suc by blast
		\<comment> \<open>Поэтому утверждение леммы верно.\<close>
	then show \<open>is_odd 0 \<or> is_odd (Suc 0)\<close> by blast
next
		\<comment> \<open>Шаг индукции.\<close>
	case (Suc n)
		\<comment> \<open>Предположение для @{term n}.\<close>
	assume \<open>is_odd n \<or> is_odd (Suc n)\<close>
		\<comment> \<open>Надо доказать.\<close>
	show \<open>is_odd (Suc n) \<or> is_odd (Suc (Suc n))\<close>
		\<comment> \<open>Рассмотрим случаи чётности @{term n}.\<close>
	proof (cases \<open>is_odd n\<close>)
			\<comment> \<open>Случай, когда @{term \<open>is_odd n\<close>} истино.\<close>
		case True
			\<comment> \<open>@{term n} нечётно.\<close>
		assume \<open>is_odd n\<close>
			\<comment> \<open>Тогда @{term \<open>n + 1\<close>} чётно.\<close>
		then have \<open>\<not> is_odd (Suc n)\<close> using odd_Suc by blast
			\<comment> \<open>А @{term \<open>n + 2\<close>} нечётно.\<close>
		then have \<open>is_odd (Suc (Suc n))\<close> using odd_Suc by blast
			\<comment> \<open>Поэтому утверждение леммы верно.\<close>
		then show \<open>is_odd (Suc n) \<or> is_odd (Suc (Suc n))\<close> by blast
	next
			\<comment> \<open>Случай, когда @{term \<open>is_odd n\<close>} ложно.\<close>
		case False
			\<comment> \<open>@{term n} чётно.\<close>
		assume \<open>\<not> is_odd n\<close>
			\<comment> \<open>Тогда @{term \<open>n + 1\<close>} нечётно.\<close>
		then have \<open>is_odd (Suc n)\<close> using odd_Suc by blast
			\<comment> \<open>Поэтому утверждение леммы верно.\<close>
		then show \<open>is_odd (Suc n) \<or> is_odd (Suc (Suc n))\<close> by blast
	qed
qed

	\<comment> \<open>Целое или следующее за ним число нечётно.\<close>
lemma successive_exclusive_is_odd: \<open>is_odd n \<noteq> is_odd (Suc n)\<close>
	\<comment> \<open>Рассмотрим случаи чётности @{term n}.\<close>
proof (cases \<open>is_odd n\<close>)
			\<comment> \<open>Случай, когда @{term \<open>is_odd n\<close>} истино.\<close>
	case True
		\<comment> \<open>@{term n} нечётно.\<close>
	assume \<open>is_odd n\<close>
		\<comment> \<open>Кроме того тогда @{term \<open>n + 1\<close>} чётно.\<close>
	moreover then have \<open>\<not> is_odd (Suc n)\<close> using odd_Suc by blast
		\<comment> \<open>Из вышесказанного следует, утверждение леммы верно.\<close>
	ultimately show \<open>is_odd n \<noteq> is_odd (Suc n)\<close> by blast
next
		\<comment> \<open>Случай, когда @{term \<open>is_odd n\<close>} ложно.\<close>
	case False
		\<comment> \<open>@{term n} чётно.\<close>
	assume \<open>\<not> is_odd n\<close>
		\<comment> \<open>Кроме того тогда @{term \<open>n + 1\<close>} нечётно.\<close>
	moreover then have \<open>is_odd (Suc n)\<close> using odd_Suc by blast
		\<comment> \<open>Из вышесказанного следует, что утверждение леммы верно.\<close>
	ultimately show \<open>is_odd n \<noteq> is_odd (Suc n)\<close> by blast
qed

lemma two_multiple_is_even: \<open>\<not> is_odd (2 * n)\<close>
proof (induction n)
	case 0
	show ?case by simp
next
	case (Suc n)
	then show ?case by simp
qed

lemma non_two_multiple_is_odd: \<open>is_odd (Suc (2 * n))\<close>
	using two_multiple_is_even odd_Suc by blast

lemma odd_even_representation: \<open>\<exists> k. n = 2 * k \<or> n = Suc (2 * k)\<close>
proof (induction n)
	case 0
	then show ?case by simp
next
	case (Suc n)
	then obtain k where \<open>n = 2 * k \<or> n = Suc (2 * k)\<close> by blast
	show ?case
	proof (cases \<open>n = 2 * k\<close>)
		case True
		then show ?thesis by blast
	next
		case False
		with \<open>n = 2 * k \<or> n = Suc (2 * k)\<close> have \<open>n = Suc (2 * k)\<close> by blast
		then have \<open>Suc n = Suc (Suc (2 * k))\<close> by blast
		then have \<open>Suc n = 2 * (Suc k)\<close> by simp
		then show ?thesis by blast
	qed
qed

lemma is_odd_mult: \<open>is_odd (x * y) \<longleftrightarrow> is_odd x \<and> is_odd y\<close>
proof -
	obtain m where
		X: \<open>x = 2 * m \<or> x = Suc (2 * m)\<close> using odd_even_representation by blast
	obtain n where
		Y: \<open>y = 2 * n \<or> y = Suc (2 * n)\<close> using odd_even_representation by blast
	show \<open>is_odd (x * y) \<longleftrightarrow> is_odd x \<and> is_odd y\<close>
	proof (cases \<open>is_odd x\<close>)
		case oddX: True
		with X have
			M: \<open>x = Suc (2 * m)\<close> using two_multiple_is_even by blast
		show ?thesis
		proof (cases \<open>is_odd y\<close>)
			case oddY: True
			with Y have \<open>y = Suc (2 * n)\<close> using two_multiple_is_even by blast
			with M have \<open>x * y = Suc (2 * m) * Suc (2 * n)\<close> by blast
			then have \<open>x * y = Suc (2 * (Suc (2 * m) * n + m))\<close> by simp
			moreover have \<open>is_odd (Suc (2 * (Suc (2 * m) * n + m)))\<close>
				using non_two_multiple_is_odd by blast
			ultimately show ?thesis using oddX oddY by simp
		next
			case evenY: False
			with Y have \<open>y = 2 * n\<close> using non_two_multiple_is_odd by blast
			with M have \<open>x * y = Suc (2 * m) * (2 * n)\<close> by blast
			then have \<open>x * y = 2 * (Suc (2 * m) * n)\<close> by simp
			moreover have \<open>\<not> is_odd (2 * (Suc (2 * m) * n))\<close>
				using two_multiple_is_even by blast
			ultimately show ?thesis using oddX evenY by simp
		qed
	next
		case evenX: False
		with X have \<open>x = 2 * m\<close> using non_two_multiple_is_odd by blast
		then have \<open>x * y = 2 * (m * y)\<close> by simp
		then have \<open>\<not> is_odd (x * y) \<longleftrightarrow> \<not> is_odd (2 * (m * y))\<close> by (simp only:)
		moreover have \<open>\<not> is_odd (2 * (m * y))\<close>
			using two_multiple_is_even by blast
		ultimately have \<open>\<not> is_odd (x * y)\<close> by simp
		with evenX show \<open>is_odd (x * y) \<longleftrightarrow> (is_odd x \<and> is_odd y)\<close> by blast
	qed
qed

lemma is_odd_foldr:
	\<open>is_odd (foldr (*) xs y) \<Longrightarrow> z \<in> set xs \<Longrightarrow> is_odd z\<close>
proof (induction xs arbitrary: y)
	case Nil
	then show \<open>is_odd z\<close> by simp
next
	case (Cons x xs)
	assume Prem: \<open>is_odd (foldr (*) (x # xs) y)\<close>
	assume IH: \<open>\<And> y. is_odd (foldr (*) xs y) \<Longrightarrow> z \<in> set xs \<Longrightarrow> is_odd z\<close>
	from Prem have \<open>is_odd (x * foldr (*) xs y)\<close> by simp
	with IH have \<open>z \<in> set xs \<Longrightarrow> is_odd z\<close> using is_odd_mult by blast
	moreover from \<open>is_odd (x * foldr (*) xs y)\<close> have \<open>is_odd x\<close>
		using is_odd_mult by blast
	moreover assume \<open>z \<in> set (x # xs)\<close>
	then have \<open>z = x \<or> z \<in> set xs\<close> by simp
	ultimately show \<open>is_odd z\<close> by blast
qed

lemma is_odd_filter:
	\<open>is_odd (foldr (*) (filter P xs) y) \<Longrightarrow> x \<in> set xs \<Longrightarrow> P x \<Longrightarrow> is_odd x\<close>
proof -
	assume \<open>is_odd (foldr (*) (filter P xs) y)\<close>
	then have \<open>\<forall> x \<in> set (filter P xs). is_odd x\<close> using is_odd_foldr by blast
	moreover assume \<open>x \<in> set xs\<close> \<open>P x\<close>
	ultimately show \<open>is_odd x\<close> by simp
qed

end