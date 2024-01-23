theory series

imports Main "HOL.Real"

begin

(* Verification of a proof for rearrangement of abs convergent series. *)

abbreviation "seqshift f N \<equiv> (\<lambda>n. f (N + n))"

abbreviation "seqpad f N \<equiv> (\<lambda>n. if n < N then 0 else f (n - N))"

lemma seqshift_commute:
  "seqshift (seqshift f N) N' = seqshift (seqshift f N') N"
  for N N' :: "'a :: ab_semigroup_add"
  using add.assoc[of N N'] add.commute[of N N'] add.assoc[of N' N] by simp

definition conv_to :: "(nat \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> bool"
  where "conv_to f L \<equiv> (\<forall>r>0. \<exists>N. range (\<lambda>n. \<bar>seqshift f N n - L\<bar>) \<subseteq> {0..<r})"

lemma topological_conv_to_iff:
  "conv_to f L = (\<forall>a. \<forall>b. L \<in> {a<..<b} \<longrightarrow> (\<exists>N. range (seqshift f N) \<subseteq> {a<..<b}))"
proof
  assume 1: "conv_to f L"
  show "\<forall>a. \<forall>b. L \<in> {a<..<b} \<longrightarrow> (\<exists>N. range (seqshift f N) \<subseteq> {a<..<b})"
  proof clarify
    fix a b assume ab: "L \<in> {a<..<b}"
    define r where "r \<equiv> min (L - a) (b - L)"
    with ab have "0 < r" by force
    with 1 obtain N where N: "range (\<lambda>n. \<bar>seqshift f N n - L\<bar>) \<subseteq> {0..<r}"
      using conv_to_def by blast
    have "range (seqshift f N) \<subseteq> {a<..<b}"
    proof clarify
      fix n show "seqshift f N n \<in> {a<..<b}"
      proof (cases "seqshift f N n \<ge> L")
        case True
        moreover from N have "\<bar>seqshift f N n - L\<bar> \<in> {0..<r}" by fast
        ultimately show ?thesis using r_def ab by fastforce
      next
        case False
        moreover from N have "\<bar>seqshift f N n - L\<bar> \<in> {0..<r}" by fast
        ultimately show ?thesis using r_def ab by fastforce
      qed
    qed
    thus "\<exists>N. range (seqshift f N) \<subseteq> {a<..<b}" by blast
  qed
next
  assume 2: "\<forall>a. \<forall>b. L \<in> {a<..<b} \<longrightarrow> (\<exists>N. range (seqshift f N) \<subseteq> {a<..<b})"
  show "conv_to f L"
    unfolding conv_to_def
  proof clarify
    fix r::real assume "0 < r"
    with 2 obtain N where N: "range (seqshift f N) \<subseteq> {L-r<..<L+r}" by fastforce
    have "range (\<lambda>n. \<bar>seqshift f N n - L\<bar>) \<subseteq> {0..<r}"
    proof clarify
     fix n
     from N have "seqshift f N n \<in> {L-r<..<L+r}" by fast
     thus "\<bar>seqshift f N n - L\<bar> \<in> {0..<r}" by fastforce
    qed
    thus "\<exists>N. range (\<lambda>n. \<bar>seqshift f N n - L\<bar>) \<subseteq> {0..<r}" by fast
  qed
qed

lemma topological_conv_toI:
  "conv_to f L"
  if "\<And>a b. L \<in> {a<..<b} \<Longrightarrow> \<exists>N. range (seqshift f N) \<subseteq> {a<..<b}"
  using that topological_conv_to_iff by blast

lemma nonneg_seq_conv_to_0:
  "conv_to f 0 = (\<forall>r>0. \<exists>N. range (seqshift f N) \<subseteq> {0..<r})"
  if "range f \<subseteq> {0..}"
proof-
  from that have "\<forall>N. \<forall>n. f (N + n) \<ge> 0" by auto
  hence *: "\<forall>N. (\<lambda>n. \<bar>seqshift f N n\<bar>) = seqshift f N" by force
  have "conv_to f 0 = (\<forall>r>0. \<exists>N. range (\<lambda>n. \<bar>seqshift f N n\<bar>) \<subseteq> {0..<r})"
    using conv_to_def by simp
  also have "\<dots> = (\<forall>r>0. \<exists>N. range (seqshift f N) \<subseteq> {0..<r})"
    using * by presburger
  finally show ?thesis by blast
qed

lemma conv_to_constant: "conv_to (\<lambda>n. c) c"
  unfolding conv_to_def by simp

lemma conv_to_seqshift: "conv_to (seqshift f N) L" if "conv_to f L"
proof (rule topological_conv_toI)
  fix a b assume "L \<in> {a<..<b}"
  with that obtain N' where N': "range (seqshift f N') \<subseteq> {a<..<b}"
    using topological_conv_to_iff by blast
  have "range (seqshift (seqshift f N) N') \<subseteq> {a<..<b}"
  proof clarify
    fix n
    have "seqshift (seqshift f N) N' n = seqshift f N' (N + n)" using seqshift_commute by meson
    with N' show "seqshift (seqshift f N) N' n \<in> {a<..<b}" by fast
  qed
  thus "\<exists>N'. range (seqshift (seqshift f N) N') \<subseteq> {a<..<b}" by blast
qed

lemma conv_to_seqpad: "conv_to (seqpad f N) L" if "conv_to f L"
proof (rule topological_conv_toI)
  fix a b assume "L \<in> {a<..<b}"
  with that obtain N' where "range (seqshift f N') \<subseteq> {a<..<b}"
    using topological_conv_to_iff by blast
  moreover define M where "M \<equiv> N + N'"
  ultimately have "range (seqshift (seqpad f N) M) \<subseteq> {a<..<b}" by auto
  thus "\<exists>M. range (seqshift (seqpad f N) M) \<subseteq> {a<..<b}" by fast
qed

lemma conv_to_homog: "conv_to (\<lambda>n. c * f n) (c * L)" if "conv_to f L"
proof (cases "c = 0")
  case True
  thus "conv_to (\<lambda>n. c * f n) (c * L)" using conv_to_constant by simp
next
  case False
  show "conv_to (\<lambda>n. c * f n) (c * L)"
    unfolding conv_to_def
  proof (standard, clarify)
    fix r :: real assume "0 < r"
    with False have "0 < r / \<bar>c\<bar>" by simp
    with that obtain N where N: "range (\<lambda>n. \<bar>seqshift f N n - L\<bar>) \<subseteq> {0..<r/\<bar>c\<bar>}"
      using conv_to_def by blast
    have "range (\<lambda>n. \<bar>c * seqshift f N n - c * L\<bar>) \<subseteq> {0..<r}"
    proof clarify
      fix n
      from N have "\<bar>seqshift f N n - L\<bar> \<in> {0..<r/\<bar>c\<bar>}" by fast
      with False have "\<bar>seqshift f N n - L\<bar> * \<bar>c\<bar> < r"
        using pos_less_divide_eq[of "\<bar>c\<bar>" "\<bar>seqshift f N n - L\<bar>" r] by simp
      hence "\<bar>c * seqshift f N n - c * L\<bar> < r"
        using abs_mult[of c "seqshift f N n - L"] by argo
      thus "\<bar>c * seqshift f N n - c * L\<bar> \<in> {0..<r}" by force
    qed
    thus "\<exists>N. range (\<lambda>n. \<bar>c * seqshift f N n - c * L\<bar>) \<subseteq> {0..<r}" by blast
  qed
qed

lemma conv_to_neg: "conv_to (\<lambda>n. - f n) (-L)" if "conv_to f L"
  using that conv_to_homog[of f L "-1"] by simp

lemma conv_to_add: "conv_to (\<lambda>n. f n + g n) (L + M)" if "conv_to f L" and "conv_to g M"
  unfolding conv_to_def
proof clarify
  fix r :: real assume "0 < r"
  hence r: "0 < r / 2" by fastforce
  from this that obtain N1 N2 where N12:
    "range (\<lambda>n. \<bar>seqshift f N1 n - L\<bar>) \<subseteq> {0..<r/2}"
    "range (\<lambda>n. \<bar>seqshift g N2 n - M\<bar>) \<subseteq> {0..<r/2}"
    unfolding conv_to_def by presburger
  define N where "N \<equiv> max N1 N2"
  have "range (\<lambda>n. \<bar>seqshift (\<lambda>m. f m + g m) N n - (L + M)\<bar>) \<subseteq> {0..<r}"
  proof clarify
    fix n
    from N_def have "N1 < Suc N" by force
    from this obtain k1 where k1: "N = N1 + k1" using less_natE by blast
    from N_def have "N2 < Suc N" by force
    from this obtain k2 where k2: "N = N2 + k2" using less_natE by blast
    from N12 have *: "\<bar>seqshift f N1 (k1 + n) - L\<bar> < r/2" "\<bar>seqshift g N2 (k2 + n) - M\<bar> < r/2" by (fastforce, fastforce)
    have
      "\<bar>seqshift (\<lambda>m. f m + g m) N n - (L + M)\<bar> =
        \<bar>(f (N1 + k1 + n) - L) + (g (N2 + k2 + n) - M)\<bar>"
      using k1 k2 by auto
    also have
      "\<dots> = \<bar>(seqshift f N1 (k1 + n) - L) + (seqshift g N2 (k2 + n) - M)\<bar>"
      by (metis add.assoc)
    finally have "\<bar>seqshift (\<lambda>m. f m + g m) N n - (L + M)\<bar> < r"
      using * by argo
    thus "\<bar>seqshift (\<lambda>m. f m + g m) N n - (L + M)\<bar> \<in> {0..<r}" by simp
  qed
  thus "\<exists>N. range (\<lambda>n. \<bar>seqshift (\<lambda>m. f m + g m) N n - (L + M)\<bar>) \<subseteq> {0..<r}" by blast
qed

lemma conv_to_shift_iff: "conv_to f L = conv_to (\<lambda>n. f n - L) 0"
proof
  show "conv_to f L \<Longrightarrow> conv_to (\<lambda>n. f n - L) 0"
    using conv_to_constant[of "-L"] conv_to_add by fastforce
  show "conv_to (\<lambda>n. f n - L) 0 \<Longrightarrow> conv_to (\<lambda>n. f n) L"
    using conv_to_constant[of L] conv_to_add by fastforce
qed

lemma conv_to_shift_iff': "conv_to f L = conv_to (\<lambda>n. L - f n) 0"
  using conv_to_shift_iff conv_to_neg[of "\<lambda>n. L - f n" 0] conv_to_neg[of "\<lambda>n. f n - L " 0] by auto

lemma conv_to_abs_shift_iff: "conv_to f L = conv_to (\<lambda>n. \<bar>f n - L\<bar>) 0"
    unfolding conv_to_def by simp

definition conv :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  where "conv f \<equiv> (\<exists>L. conv_to f L)"

lemma conv_constant: "conv (\<lambda>n. c)"
  using conv_to_constant conv_def by auto

lemma conv_seqshift: "conv (seqshift f N)" if "conv f"
  using that conv_to_seqshift unfolding conv_def by fast

lemma conv_seqpad: "conv (seqpad f N)" if "conv f"
  using that conv_to_seqpad unfolding conv_def by auto

lemma conv_homog: "conv (\<lambda>n. c * f n)" if "conv f"
  using that conv_to_homog conv_def by auto

lemma conv_neg: "conv (\<lambda>n. - f n)" if "conv f"
  using that conv_to_neg conv_def by auto

lemma conv_add: "conv (\<lambda>n. f n + g n)" if "conv f" and "conv g"
  using that conv_to_add conv_def by metis

lemma monotone_conv: "conv_to f (Sup (range f))" if "mono f" and "bdd_above (range f)"
proof (rule topological_conv_toI)
  define L where "L \<equiv> Sup (range f)"
  fix a b assume ab: "L \<in> {a<..<b}"
  have "\<not> (range f \<subseteq> {..a})"
  proof
    assume "range f \<subseteq> {..a}"
    moreover have "range f \<noteq> {}" by fastforce
    ultimately have "L \<le> a"
      using L_def cSup_least[of "range f" a] by blast
    with ab show False by simp
  qed
  from this obtain N where N: "\<not> (f N \<le> a)" by blast
  have "range (seqshift f N) \<subseteq> {a<..<b}"
  proof clarify
    fix n show "seqshift f N n \<in> {a<..<b}"
    proof (induct n)
      case 0 from that(2) L_def ab N show ?case using cSup_upper[of "f N" "range f"] by auto
    next
      case (Suc n)
      moreover from that(1) have "seqshift f N n \<le> seqshift f N (Suc n)" using monoD by fastforce
      ultimately show ?case
        using that(2) L_def ab cSup_upper[of "seqshift f N (Suc n)" "range f"] by force
    qed
  qed
  thus "\<exists>N. range (seqshift f N) \<subseteq> {a<..<b}" by fast
qed

lemma monotone_conv': "conv f" if "mono f" and "bdd_above (range f)"
  using that monotone_conv conv_def by blast

lemma conv_imp_bdd_above: "bdd_above (range f)" if "conv f"
  unfolding bdd_above_def
proof-
  from that obtain L where "conv_to f L" using conv_def by auto
  from this obtain N where N: "range (seqshift f N) \<subseteq> {L-1<..<L+1}"
    using topological_conv_to_iff by fastforce
  define M where "M \<equiv> Max (f ` {0..<N} \<union> {L + 1})"
  have "\<forall>x\<in>range f. x \<le> M"
  proof clarify
    fix n show "f n \<le> M"
    proof (cases "n < N")
      case True
      with M_def show ?thesis using Max_ge[of "f ` {0..<N} \<union> {L + 1}" "f n"] by simp
    next
      case False
      hence "N < Suc n" by simp
      from this obtain k where "n = N + k" using less_natE by blast
      with N have "f n < L + 1" by fastforce
      moreover from M_def have "L + 1 \<le> M"
        using Max_ge[of "f ` {0..<N} \<union> {L + 1}" "L + 1"] by blast
      ultimately show ?thesis by auto
    qed
  qed
  thus "\<exists>M. \<forall>x\<in>range f. x \<le> M" by blast
qed

abbreviation "partsum f n \<equiv> sum f {0..n}"

definition sconv :: "(nat \<Rightarrow> real) \<Rightarrow> bool"
  where "sconv f \<equiv> conv (partsum f)"

abbreviation "sconv_to f S \<equiv> conv_to (partsum f) S"

abbreviation "abs_sconv f \<equiv> sconv (abs \<circ> f)"

lemma sconv_homog: "sconv (\<lambda>n. c * f n)" if "sconv f"
  unfolding sconv_def
proof-
  from that have "conv (\<lambda>n. c * partsum f n)"
    using sconv_def conv_homog by blast
  moreover have "\<forall>n. c * partsum f n = partsum (\<lambda>n. c * f n) n"
    using sum_distrib_left by blast
  ultimately show "conv (partsum (\<lambda>n. c * f n))" by simp
qed

lemma sconv_neg: "sconv (\<lambda>n. - f n)" if "sconv f"
  using that sconv_homog[of f "-1"] by force

lemma sconv_add: "sconv (\<lambda>n. f n + g n)" if "sconv f" and "sconv g"
  using that sconv_def conv_add sum.distrib[of f g] by force

lemma nonneg_sum_mono:
  "finite B \<Longrightarrow> f ` B \<subseteq> {0..} \<Longrightarrow> A \<subseteq> B \<Longrightarrow> sum f A \<le> sum f B" for f :: "'a \<Rightarrow> real"
proof (induct B arbitrary: A rule: finite_induct, simp)
  case (insert b B)
  show ?case
  proof (cases "b \<in> A")
    case False with insert(1,2,4,5) insert(3)[of A] show ?thesis using sum.insert by fastforce
  next
    case True
    moreover from insert(4,5) insert(3)[of "A - {b}"] have "sum f (A - {b}) \<le> sum f B" by blast
    ultimately show "sum f A \<le> sum f (insert b B)"
      using sum.remove[of A b f] sum.insert[of B b f] insert(1,2,5) finite_subset[of A "insert b B"]
      by    fastforce
  qed
qed

lemma mono_nonneg_partsum:
  "mono (partsum f)" if "range f \<subseteq> {0..}" for f :: "nat \<Rightarrow> real"
proof
  fix n n' from that show "n \<le> n' \<Longrightarrow> partsum f n \<le> partsum f n'"
    using nonneg_sum_mono[of "{0..n'}" f] by fastforce
qed

lemma sconv_compare:
  "sconv f" if "sconv g" and "range f \<subseteq> {0..}" and "\<forall>n. f n \<le> g n"
  unfolding sconv_def
proof (rule monotone_conv', rule mono_nonneg_partsum, rule that(2))
  have *: "\<forall>n. partsum f n \<le> partsum g n"
  proof
    fix n show "partsum f n \<le> partsum g n"
    proof (induct n)
      case 0 from that(3) show ?case by simp
    next
      case (Suc n)
      moreover from that(3) have "f (Suc n) \<le> g (Suc n)" by blast
      ultimately show ?case by simp
    qed
  qed
  show "bdd_above (range (partsum f))"
    unfolding bdd_above_def
  proof-
    from that(1) have "bdd_above (range (partsum g))" using conv_imp_bdd_above sconv_def by metis
    from this obtain M where M: "\<forall>x\<in>range (partsum g). x \<le> M"
      using bdd_above_def by meson
    have "\<forall>x\<in>range (partsum f). x \<le> M"
    proof clarify
      fix n
      from * have "partsum f n \<le> partsum g n" by metis
      also have "\<dots> \<le> M" using M by blast
      finally show "partsum f n \<le> M" by blast
    qed
    thus "\<exists>M. \<forall>x\<in>range (partsum f). x \<le> M" by blast
  qed
qed

lemma partsum_seqshift:
  "partsum (seqshift f N) n = seqshift (partsum f) N n - partsum f (N - 1)"
  if "0 < N" for f :: "nat \<Rightarrow> real"
proof-
  from that obtain N' where "N = Suc N'" using less_natE by meson
  hence "seqshift (partsum f) N 0 - partsum f (N - 1) = f N" by simp
  thus ?thesis by (induct n) auto
qed

lemma sconv_to_tail_sum:
  "sconv_to (seqshift f N) (S - partsum f (N-1))"
  if "0 < N" and "sconv_to f S"
proof (rule topological_conv_toI)
  define pN where "pN \<equiv> partsum f (N-1)"
  fix a b assume "S - pN \<in> {a<..<b}"
  hence "S \<in> {a+pN<..<b+pN}" by simp
  with that(2) obtain N' where N': "range (seqshift (partsum f) N') \<subseteq> {a+pN<..<b+pN}"
    using topological_conv_to_iff by meson
  have "range (seqshift (partsum (seqshift f N)) N') \<subseteq> {a<..<b}"
  proof clarify
    fix n
    from N' have "seqshift (partsum f) N' (N + n) \<in> {a+pN<..<b+pN}" by fast
    hence "seqshift (partsum f) N' (N + n) - pN \<in> {a<..<b}" by auto
    with that(1) pN_def show
      "seqshift (partsum (seqshift f N)) N' n \<in> {a<..<b}"
      using partsum_seqshift[of N f] add.assoc[of N N' n] add.commute[of N N'] add.assoc[of N' N n]
      by    metis
  qed
  thus "\<exists>N'. range (seqshift (partsum (seqshift f N)) N') \<subseteq> {a<..<b}" by meson
qed

lemma sconv_seqshift:
  "sconv (seqshift f N)" if "sconv f"
proof (cases "N = 0")
  case True with that show ?thesis by simp
next
  case False with that show ?thesis using sconv_to_tail_sum conv_def sconv_def by auto
qed

lemma partsum_seqpad: "partsum (seqpad f N) = seqpad (partsum f) N" for N :: nat
proof
  fix n :: nat show "partsum (seqpad f N) n = seqpad (partsum f) N n"
  proof (induct n)
    case 0 show ?case by fastforce
  next
    case (Suc n)
    hence "partsum (seqpad f N) (Suc n) = seqpad (partsum f) N n + seqpad f N (Suc n)"
      by force
    have "seqpad (partsum f) N (Suc n) = (if Suc n < N then 0 else partsum f (Suc n - N))"
      by blast
    show ?case
    proof (cases "n < N" "Suc n < N" rule: case_split[case_product case_split])
      case True_True with Suc show ?thesis by force
    next
      case True_False with Suc show ?thesis by force
    next
      case False_True then show ?thesis by force
    next
      case False_False
      moreover from this have "Suc n - N = Suc (n - N)" by linarith
      ultimately show ?thesis using Suc by auto
    qed
  qed
qed

lemma sconv_seqpad: "sconv (seqpad f N)" if "sconv f"
proof-
  from that have "conv (partsum f)" using sconv_def by fast
  thus ?thesis using conv_seqpad partsum_seqpad[of N f] sconv_def by auto
qed

lemma sconv_imp_conv_to_0: "conv_to f 0" if "sconv f"
proof-
  from that obtain S where "sconv_to f S" using sconv_def conv_def by blast
  moreover from this have "conv_to (seqpad (partsum f) 1) S" using conv_to_seqpad by fast
  ultimately have "conv_to (\<lambda>n. partsum f n - seqpad (partsum f) 1 n) 0"
    using conv_to_neg conv_to_add by fastforce
  moreover have "(\<lambda>n. partsum f n - seqpad (partsum f) 1 n) = f"
  proof
    fix n
    show "partsum f n - seqpad (partsum f) 1 n = f n"
    proof (cases "n < 1", simp)
      case False
      hence *: "n = Suc (n - 1)" by simp
      from False have
        "partsum f n - seqpad (partsum f) 1 n = partsum f (Suc (n - 1)) - partsum f (n - 1)"
        by simp
      also have "\<dots> = f (Suc (n - 1))" by simp
      finally show ?thesis using * by presburger
    qed
  qed
  ultimately show ?thesis by argo
qed

lemma abs_sconv: "sconv f" if "abs_sconv f"
proof-
  have "sconv (\<lambda>n. f n + \<bar>f n\<bar>)"
  proof (rule sconv_compare)
    from that show "sconv (\<lambda>n. 2 * \<bar>f n\<bar>)" using sconv_homog by fastforce
    show "range (\<lambda>n. f n + \<bar>f n\<bar>) \<subseteq> {0..}" by auto
    show "\<forall>n. f n + \<bar>f n\<bar> \<le> 2 * \<bar>f n\<bar>" by fastforce
  qed
  moreover from that have "sconv (\<lambda>n. - \<bar>f n\<bar>)" using sconv_neg[of "abs \<circ> f"] by simp
  ultimately show "sconv f" using sconv_add by fastforce
qed

abbreviation "nonneg_sconv_lim f \<equiv> Sup (range (partsum f))"

lemma nonneg_sconv_lim_ge:
  "partsum f N \<le> nonneg_sconv_lim f"
   if "range f \<subseteq> {0..}" and "sconv f"
  using that cSup_upper[of _ "range (partsum f)"] conv_imp_bdd_above sconv_def by force

lemma nonneg_sconv_to:
  "sconv_to f (nonneg_sconv_lim f)" if "range f \<subseteq> {0..}" and "sconv f"
  using that monotone_conv mono_nonneg_partsum conv_imp_bdd_above sconv_def by meson

lemma noneg_part_partsum_mono:
  "sum f A \<le> nonneg_sconv_lim f - partsum f N"
  if "range f \<subseteq> {0..}" and "sconv f" and "finite A" and "A \<subseteq> {N<..}"
proof (cases "A = {}")
  case True
  with that(1,2) show ?thesis using nonneg_sconv_lim_ge by simp
next
  case False
  define M where "M \<equiv> Max A"
  from that(4) have "{0..N} \<inter> A = {}" by fastforce
  with that(3) have "partsum f N + sum f A = sum f ({0..N} \<union> A)"
    using sum.union_disjoint[of "{0..N}" A f] by fastforce
  also have "\<dots> \<le> partsum f M"
  proof (rule nonneg_sum_mono, simp)
    from that(1) show "f ` {0..M} \<subseteq> {0..}" by fast
    from that(3) M_def have "A \<subseteq> {0..M}" using Max_ge by force
    moreover have "N \<le> M"
    proof-
      from False obtain a where "a \<in> A" by blast
      moreover from this that(4) have "N < a" by auto
      ultimately show "N \<le> M" using that(3) M_def Max_ge[of A a] by linarith
    qed
    ultimately show "{0..N} \<union> A \<subseteq> {0..M}" by simp
  qed
  also from that(1,2) have "\<dots> \<le> nonneg_sconv_lim f" using nonneg_sconv_lim_ge by blast
  finally have "partsum f N + sum f A \<le> nonneg_sconv_lim f" by linarith
  thus ?thesis by linarith
qed

abbreviation "abs_partsum f \<equiv> partsum (abs \<circ> f)"
abbreviation "abs_sconv_to f \<equiv> sconv_to (abs \<circ> f)"
abbreviation "abs_sconv_lim f \<equiv> Sup (range (abs_partsum f))"

lemma abs_sconv_to:
  "abs_sconv_to f (abs_sconv_lim f)" if "abs_sconv f"
  using that nonneg_sconv_to[of "abs \<circ> f"] by fastforce

lemma part_abs_partsum_mono:
  "sum (abs \<circ> f) A \<le> abs_sconv_lim f - abs_partsum f N"
  if "abs_sconv f" and "finite A" and "A \<subseteq> {N<..}"
  using that noneg_part_partsum_mono[of "abs \<circ> f"] by fastforce

theorem abs_sconv_rearrange:
  "sconv_to (f \<circ> p) S" if "bij p" and "abs_sconv f" and "sconv_to f S"
  unfolding conv_to_def
proof clarify
  fix r::real assume "0 < r"
  hence r: "0 < r/2" by auto
  from r that(3) obtain N1 where N1:
    "range (\<lambda>n. \<bar>seqshift (partsum f) N1 n - S\<bar>) \<subseteq> {0..<r/2}"
    using conv_to_def by meson
  from that(2) have *: "conv_to (\<lambda>n. abs_sconv_lim f - abs_partsum f n) 0"
    using abs_sconv_to conv_to_shift_iff' by presburger
  have "\<forall>r>0. \<exists>N. range (seqshift (\<lambda>n. abs_sconv_lim f - abs_partsum f n) N) \<subseteq> {0..<r}"
  proof (rule iffD1, rule nonneg_seq_conv_to_0, standard, clarify)
    fix n
    have "abs_partsum f n \<le> abs_sconv_lim f"
    proof (rule cSup_upper, simp, rule conv_imp_bdd_above)
      from that(2) show "conv (abs_partsum f)" using sconv_def by blast
    qed
    thus "0 \<le> abs_sconv_lim f - abs_partsum f n" by linarith
  qed (rule *)
  from this r obtain N2 where N2:
    "range (seqshift (\<lambda>n. abs_sconv_lim f - abs_partsum f n) N2) \<subseteq> {0..<r/2}"
    by blast
  define N where "N = max N1 N2"
  from N_def have "N1 < Suc N" by simp
  from this obtain N1' where N1': "N = N1 + N1'" using less_natE by blast
  from N_def have "N2 < Suc N" by simp
  from this obtain N2' where N2': "N = N2 + N2'" using less_natE by blast
  define M where "M \<equiv> Max (inv p ` {0..N})"
  have 1: "\<forall>m\<ge>M. \<bar>partsum (f \<circ> p) m - partsum f N\<bar> < r/2"
  proof clarify
    fix m assume m: "M \<le> m"
    have "{0..N} \<subseteq> p ` {0..m}"
    proof
      fix n assume "n \<in> {0..N}"
      with M_def m have "inv p n \<in> {0..m}" using Max_ge by auto
      moreover from that(1) have "n = p (inv p n)" using bij_inv_eq_iff[of p _ n] by force
      ultimately show "n \<in> p ` {0..m}" by fast
    qed
    hence "sum f (p ` {0..m}) = sum f (p ` {0..m} - {0..N}) + sum f {0..N}"
      using sum.subset_diff[of "{0..N}" "p ` {0..m}"] by fast
    with that(1) have
      "\<bar>partsum (f \<circ> p) m - partsum f N\<bar> = \<bar>sum f (p ` {0..m} - {0..N})\<bar>"
      using bij_is_inj[of p] inj_on_subset[of p UNIV "{0..m}"] sum.reindex[of p "{0..m}" f]
      by    simp
    also have "\<dots> \<le> sum (\<lambda>n. \<bar>f n\<bar>) (p ` {0..m} - {0..N})"
      using sum_abs by blast
    also have "\<dots> = sum (abs \<circ> f) (p ` {0..m} - {0..N})" by simp
    also from that(2) N2' have "\<dots> \<le> seqshift (\<lambda>n. abs_sconv_lim f - abs_partsum f n) N2 N2'"
      using part_abs_partsum_mono[of f "p ` {0..m} - {0..N}" N] by fastforce
    also from N2 have "\<dots> < r/2" by force
    finally show "\<bar>partsum (f \<circ> p) m - partsum f N\<bar> < r/2" by blast
  qed
  have "range (\<lambda>n. \<bar>seqshift (partsum (f \<circ> p)) M n - S\<bar>) \<subseteq> {0..<r}"
  proof clarify
    fix n
    from N1' have
      "\<bar>seqshift (partsum (f \<circ> p)) M n - S\<bar>
        \<le> \<bar>partsum (f \<circ> p) (M + n) - partsum f N\<bar> + \<bar>seqshift (partsum f) N1 N1' - S\<bar>"
      by fastforce
    moreover have "\<bar>partsum (f \<circ> p) (M + n) - partsum f N\<bar> < r/2"
      using 1 by force
    moreover from N1 have "\<bar>seqshift (partsum f) N1 N1' - S\<bar> < r/2" by fastforce
    ultimately have "\<bar>seqshift (partsum (f \<circ> p)) M n - S\<bar> < r" by argo
    thus "\<bar>seqshift (partsum (f \<circ> p)) M n - S\<bar> \<in> {0..<r}" by auto
  qed
  thus "\<exists>M. range (\<lambda>n. \<bar>seqshift (partsum (f \<circ> p)) M n - S\<bar>) \<subseteq> {0..<r}" by blast
qed


end

