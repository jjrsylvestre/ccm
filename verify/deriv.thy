theory deriv

imports Main "HOL.Real"

begin

(* This file verifies that my alternative definition of the derivative is equivalent to the traditional one. *)

definition def1 :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
	where "def1 q t D \<equiv> (\<forall>\<epsilon>::real. \<epsilon> > 0 \<longrightarrow> (\<exists>\<delta>::real. \<delta> > 0 \<and> (\<forall>h::real. (h \<noteq> 0 \<and> abs(h) < \<delta>) \<longrightarrow> abs(D - (q(t + h) - q(t)) / h) < \<epsilon>)))"

definition def2 :: "(real \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool"
	where "def2 q t D \<equiv> (\<forall>\<epsilon>::real. \<epsilon> > 0 \<longrightarrow> (\<exists>\<delta>::real. \<delta> > 0 \<and> (\<forall>t0::real. \<forall>t1::real. (t0 \<le> t \<and> t \<le> t1 \<and> t1 - t0 \<noteq> 0 \<and> t1 - t0 < \<delta>)\<longrightarrow> abs(D - (q(t1) - q(t0)) / (t1 - t0)) < \<epsilon>)))"

lemma (in field) diff_quotient: "(a - b) / (c - d) = (b - a) / (d - c)"
proof-
	have "(a - b) / (c - d) = - ( (a - b) / (d - c) )" by (simp add: minus_divide_right)
	thus ?thesis by (simp add: minus_divide_left)
qed

lemma "def1 = def2"
proof (standard, standard, standard)
	fix q t D
	show "def1 q t D = def2 q t D"
	proof
		assume 1: "def1 q t D"
		show "def2 q t D"
			unfolding def2_def
		proof (standard, clarify)
			fix e :: real assume "e > 0"
			with 1 obtain d :: real
				where d: "d > 0" "\<forall>h::real. (h \<noteq> 0 \<and> abs(h) < d) \<longrightarrow> abs(D - (q(t + h) - q(t)) / h) < e"
				unfolding def1_def by blast
			have "\<forall>t0 t1. t0 \<le> t \<and> t \<le> t1 \<and> t1 - t0 \<noteq> 0 \<and> t1 - t0 < d \<longrightarrow> \<bar>D - (q t1 - q t0) / (t1 - t0)\<bar> < e"
			proof (standard, standard, clarify)
				fix t0 t1 :: real
				assume t0: "t0 \<le> t" and t1: "t \<le> t1" and t1_t0_n0: "t1 - t0 \<noteq> 0" and t1_t0_ld: "t1 - t0 < d"
				show "\<bar>D - (q t1 - q t0) / (t1 - t0)\<bar> < e"
				proof (cases "t0 = t" "t1 = t" rule: case_split[case_product case_split])
					case True_True with t1_t0_n0 show ?thesis by force
				next
					case True_False
					define h where "h \<equiv> t1 - t0"
					with t0 t1 t1_t0_ld have "\<bar>h\<bar> < d" by force
					with True_False d(2) t1_t0_n0 h_def show ?thesis by fastforce
				next
					case False_True
					define h where "h \<equiv> t0 - t1"
					with t0 t1 t1_t0_ld have "\<bar>h\<bar> < d" by force
					moreover from h_def t1_t0_n0 have "h \<noteq> 0" by force
					ultimately have "abs(D - (q(t + h) - q(t)) / h) < e" using d(2) by presburger
					with False_True h_def show ?thesis by (simp add: diff_quotient)
				next
					case False_False
					define dt where "dt \<equiv> t1 - t0"
					define dtL where "dtL \<equiv> t - t0"
					define dtR where "dtR \<equiv> t1 - t"
					define A where "A \<equiv> dtR * ( D - (q t1 - q t) / dtR )"
					define B where "B \<equiv> dtL * ( D - (q t - q t0) / dtL )"
					have dt_g0: "dt > 0" using t0 t1 t1_t0_n0 dt_def by simp
					hence dt_ne_0: "dt \<noteq> 0" using dt_g0 by simp
					have "\<bar> A + B \<bar> \<le> \<bar>A\<bar> + \<bar>B\<bar>" by force
					with dt_g0 have A_B_dt: "\<bar> A + B \<bar> / dt \<le> (\<bar>A\<bar> + \<bar>B\<bar>) / dt" by (simp add: divide_right_mono)
					have dtL_g0: "dtL > 0" using False_False(1) t0 unfolding dtL_def by auto
					hence dtL_n0: "dtL \<noteq> 0" by auto
					hence "- dtL \<noteq> 0" by simp
					moreover have "\<bar>- dtL\<bar> < d" using t0 t1 t1_t0_ld unfolding dtL_def by simp
					ultimately have "\<bar>D - (q (t + - dtL) - q t) / (- dtL)\<bar> < e"
						using d(2) by blast
					with dtL_def dtL_g0 have D_dtL: "dtL * \<bar>D - (q t - q t0) / dtL\<bar> < dtL * e" by (simp add: diff_quotient)
					have dtR_g0: "dtR > 0" using False_False(2) t1 unfolding dtR_def by argo
					hence dtR_n0: "dtR \<noteq> 0" by simp
					moreover have "\<bar>dtR\<bar> < d" using t0 t1 t1_t0_ld unfolding dtR_def by simp
					ultimately have "\<bar>D - (q (t + dtR) - q t) / dtR\<bar> < e"
						using d(2) by blast
					with dtR_def dtR_g0 have D_dtR: "dtR * \<bar>D - (q t1 - q t) / dtR\<bar> < dtR * e" by simp
					with D_dtL have
						"dtR * \<bar>D - (q t1 - q t) / dtR\<bar> + dtL * \<bar>D - (q t - q t0) / dtL\<bar> < dtR * e + dtL * e"
						by argo
					with dt_g0 have
						"(dtR * \<bar>D - (q t1 - q t) / dtR\<bar> + dtL * \<bar>D - (q t - q t0) / dtL\<bar>) / dt < ( (dtR + dtL) * e ) / dt"
						using distrib_right[of dtR dtL e] divide_strict_right_mono by metis
					moreover have dtL_plus_dtR: "dtR + dtL = dt" unfolding dt_def dtL_def dtR_def by argo
					ultimately have
						*: "(dtR * \<bar>D - (q t1 - q t) / dtR\<bar> + dtL * \<bar>D - (q t - q t0) / dtL\<bar>) / dt < e"
						using dt_ne_0 nonzero_mult_div_cancel_left by simp
					from dt_ne_0 have
						"\<bar>D - (q t1 - q t0) / (t1 - t0)\<bar> = \<bar>(dt * D - ( dtR * ( (q t1 - q t) / dtR ) + (q t - q t0) * (dtL / dtL) ) ) / dt \<bar>"
						using dt_def dtR_n0 dtL_n0 by (simp add: field_simps)
					also have "\<dots> = \<bar>(dtR * D + dtL * D - ( dtR * ( (q t1 - q t) / dtR ) ) - ( dtL * ( (q t - q t0) / dtL ) ) ) / dt \<bar>"
						using dtL_plus_dtR distrib_right[of dtR dtL D] by (simp add: diff_diff_add)
					also have "\<dots> = \<bar>A + B\<bar> / dt" using dt_g0 by (simp add: algebra_simps A_def B_def)
					also have "\<dots> \<le> (\<bar>A\<bar> + \<bar>B\<bar>) / dt" using abs_triangle_ineq[of A B] dt_g0 A_B_dt by blast
					also have "\<dots> = (dtR * \<bar>D - (q t1 - q t) / dtR\<bar> + dtL * \<bar>D - (q t - q t0) / dtL\<bar>) / dt"
						using A_def B_def dtR_g0 abs_mult[of dtR] dtL_g0 abs_mult[of dtL] by force
					also have "\<dots> < e" using * by blast
					finally show ?thesis by fast
				qed
			qed
			with d(1) show
				"\<exists>d>0. \<forall>t0 t1. t0 \<le> t \<and> t \<le> t1 \<and> t1 - t0 \<noteq> 0 \<and> t1 - t0 < d \<longrightarrow> \<bar>D - (q t1 - q t0) / (t1 - t0)\<bar> < e"
				by blast
		qed
	next
		assume 2: "def2 q t D"
		show "def1 q t D"
			unfolding def1_def
		proof (standard, clarify)
			fix e :: real assume "e > 0"
			with 2 obtain d :: real
				where d: "d > 0" "\<forall>t0 t1. t0 \<le> t \<and> t \<le> t1 \<and> t1 - t0 \<noteq> 0 \<and> t1 - t0 < d \<longrightarrow> \<bar>D - (q t1 - q t0) / (t1 - t0)\<bar> < e"
				unfolding def2_def by blast
			have "\<forall>h. (h \<noteq> 0 \<and> \<bar>h\<bar> < d) \<longrightarrow> \<bar>D - (q (t + h) - q t) / h\<bar> < e"
			proof (standard, clarify)
				fix h :: real assume h: "h \<noteq> 0" "\<bar>h\<bar> < d"
				show "\<bar>D - (q (t + h) - q t) / h\<bar> < e"
				proof (cases "h > 0")
					case True
					define t1 :: real where "t1 \<equiv> t + h"
					with h True have "t \<le> t" "t \<le> t1" "t1 - t \<noteq> 0" "t1 - t < d"
						by auto
					with d(2) have "\<bar>D - (q t1 - q t) / (t1 - t)\<bar> < e" by blast
					with t1_def show ?thesis by force
				next
					case False
					define t0 :: real where "t0 \<equiv> t + h"
					with h False have "t0 \<le> t" "t \<le> t" "t - t0 \<noteq> 0" "t - t0 < d"
						by auto
					with d(2) have *: "\<bar>D - (q t - q t0) / (t - t0)\<bar> < e" by blast
					with t0_def show ?thesis by (force simp add: minus_divide_left)
				qed
			qed
			with d(1) show "\<exists>d>0. \<forall>h. (h \<noteq> 0 \<and> \<bar>h\<bar> < d) \<longrightarrow> \<bar>D - (q (t + h) - q t) / h\<bar> < e" by blast
		qed
	qed
qed

end

