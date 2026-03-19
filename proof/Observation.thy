theory Observation
  imports Main History
begin

section \<open>Observations\<close>

text \<open>Fundamentally, an observation is a set of objects and observed transactions over them.\<close>

datatype observation = Observation "object set" "otxn set"

text \<open>We define some basic accessors...\<close>

primrec all_otxns :: "observation \<Rightarrow> otxn set" where
"all_otxns (Observation objs txns) = txns"

instantiation observation :: all_objects
begin
primrec all_objects_observation :: "observation \<Rightarrow> object set" where
"all_objects_observation (Observation objs txns) = objs"
instance ..
end

instantiation observation :: all_versions
begin
primrec all_versions_observation :: "observation \<Rightarrow> version set" where
"all_versions_observation (Observation objs txns) = \<Union>{all_versions t | t. t \<in> txns}"
instance ..
end

instantiation observation :: all_oops
begin
primrec all_oops_observation :: "observation \<Rightarrow> oop set" where
"all_oops_observation (Observation objs txns) = \<Union>{all_oops t | t. t \<in> txns}"
instance ..
end

text \<open>A well-formed observation is made up of well-formed objects and transactions, and its
transactions are over those objects.\<close>

primrec wf_observation :: "observation \<Rightarrow> bool" where
"wf_observation (Observation objs txns) =
  ((\<forall>obj. obj \<in> objs \<longrightarrow> wf_object obj) \<and>
   (\<forall>t. t \<in> txns \<longrightarrow> (wf_otxn t \<and> (\<forall>oop. (oop \<in> (all_oops t)) \<longrightarrow>
                                          (\<exists>!obj. (obj \<in> objs) \<and> ((key oop) = (key obj)))))))"


text \<open>We say an observation is compatible with a history via relation m if they have the same
object set, the same number of transactions, and m is a bijective mapping from observed transactions
in the observation to compatible abstract transactions in the history.\<close>

definition is_compatible_observation :: "observation \<Rightarrow> (otxn \<Rightarrow> atxn) \<Rightarrow> history \<Rightarrow> bool" where
"is_compatible_observation obs m h =
  ((all_objects obs = all_objects h) \<and>
   (\<forall>otxn. otxn \<in> (all_otxns obs) \<longrightarrow> (is_compatible_txn otxn (m otxn))))"


section \<open>Interpretations\<close>

text \<open>An interpretation of an observation O is a history H and a bijection M which translates
operations in O to compatible observations in H. Interpretation is a reserved word, so...\<close>

datatype interp = Interp "observation" "(otxn \<Rightarrow> atxn)" "history"

primrec history :: "interp \<Rightarrow> history" where
"history (Interp obs m h) = h"

text \<open>We say f is a total bijection between a and b iff f is bijective and every a maps to a b.
I feel like there should be something for this in Isabelle already but I'm not sure.\<close>

text \<open>Giuliano: you can use the query panel to search for constants or theorems. 
Here, look for a constant of the following type: "(_ \<Rightarrow> _) \<Rightarrow> _ set \<Rightarrow> _ set \<Rightarrow> bool", and it will find:\<close>
thm Fun.bij_betw_def \<comment> \<open>That is probably what you wanted\<close>

text \<open>Giuliano correctly pointed out that bij f asserts global bijectivity, not bijectivity between
the specific sets. The correct notion is bij_betw from Isabelle's library, which asserts that f is
injective on as and the image of as under f is exactly bs.\<close>

definition total_bij :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'b set \<Rightarrow> bool" where
"total_bij f as bs \<equiv> bij_betw f as bs"

text \<open>Without the a \<in> as assumption, this still does not hold -- even with bij_betw.\<close>
lemma "(total_bij f as bs \<and> (b = (f a))) \<longrightarrow> (b \<in> bs)"
  nitpick
  oops

lemma my_lemma:
  assumes "total_bij f as bs" and "b = f a" and "a \<in> as"
  shows "(b \<in> bs)"
  using assms unfolding total_bij_def bij_betw_def by blast

lemma my_lemma_bad:
  "total_bij f as bs \<and> b = f a \<and> a \<in> as \<longrightarrow> b \<in> bs"
  unfolding total_bij_def bij_betw_def by blast

text \<open>With bij_betw, the image equality now holds, since bij_betw f a b implies f ` a = b.\<close>

lemma total_bij_image: "(total_bij f a b) \<Longrightarrow> ((f`a) = b)"
  unfolding total_bij_def bij_betw_def by simp

lemma total_bij_inj_on: "total_bij f as bs \<Longrightarrow> inj_on f as"
  unfolding total_bij_def bij_betw_def by simp

lemma total_bij_surj: "total_bij f as bs \<Longrightarrow> b \<in> bs \<Longrightarrow> \<exists>a \<in> as. f a = b"
  unfolding total_bij_def bij_betw_def by (auto simp: image_def)

text \<open>Well-formed interpretations are made up of a well-formed observation, a bijection between
observed and abstract transactions, and a well-formed history, such that the observation and 
the history are compatible via that bijection.\<close>

primrec wf_interpretation :: "interp \<Rightarrow> bool" where
"wf_interpretation (Interp obs m h) = ((wf_observation obs) \<and>
                                       (wf_history h) \<and>
                                       (total_bij m (all_otxns obs) (all_atxns h)) \<and>
                                       (is_compatible_observation obs m h))"

text \<open>This lets us talk about corresponding transactions via that bijection m.\<close>

primrec corresponding_atxn :: "interp \<Rightarrow> otxn \<Rightarrow> atxn" where
"corresponding_atxn (Interp obs m h) otxn = (m otxn)"

text \<open>The inverse direction uses THE (definite description) scoped to the observed transactions,
where injectivity of m is guaranteed by bij_betw.\<close>

primrec corresponding_otxn :: "interp \<Rightarrow> atxn \<Rightarrow> otxn" where
"corresponding_otxn (Interp obs m h) atxn = (THE otxn. otxn \<in> all_otxns obs \<and> atxn = m otxn)"

text \<open>These are invertible, thanks to m being bijective on the observed transactions.\<close>

lemma corresponding_otxn_exists:
  assumes "wf_interpretation (Interp obs m h)" and "atxn \<in> all_atxns h"
  shows "\<exists>ot \<in> all_otxns obs. m ot = atxn"
proof -
  from assms(1) have "bij_betw m (all_otxns obs) (all_atxns h)"
    by (simp add: total_bij_def)
  then have "m ` (all_otxns obs) = all_atxns h" by (simp add: bij_betw_def)
  with assms(2) show ?thesis by (metis imageE)
qed

lemma corresponding_invertible:
  assumes "wf_interpretation (Interp obs m h)" and "t \<in> all_otxns obs"
  shows "corresponding_otxn (Interp obs m h) (corresponding_atxn (Interp obs m h) t) = t"
proof -
  have inj: "inj_on m (all_otxns obs)"
    using assms(1) by (simp add: total_bij_def bij_betw_def)
  have "corresponding_atxn (Interp obs m h) t = m t" by simp
  moreover have "corresponding_otxn (Interp obs m h) (m t) =
    (THE otxn. otxn \<in> all_otxns obs \<and> m t = m otxn)" by simp
  moreover have "(THE otxn. otxn \<in> all_otxns obs \<and> m t = m otxn) = t"
  proof (rule the_equality)
    show "t \<in> all_otxns obs \<and> m t = m t" using assms(2) by simp
  next
    fix otxn
    assume "otxn \<in> all_otxns obs \<and> m t = m otxn"
    then show "otxn = t" using inj assms(2) by (auto dest: inj_onD)
  qed
  ultimately show ?thesis by simp
qed

section \<open>Recoverability\<close>

text \<open>Recoverability allows us to (in some cases) map a version of some key to a specific
observed transaction which must have produced it. To start, we figure out when a transaction
could have written a particular version of an object: some write resulting in this version of the
object is compatible with a write in the transaction.\<close>

definition could_have_been_written_by :: "object \<Rightarrow> version \<Rightarrow> otxn \<Rightarrow> bool" where
"could_have_been_written_by obj v t \<equiv> (\<exists>aw ow. aw \<in> awrites_of obj v \<and>
                                               ow \<in> all_owrites t \<and>
                                               is_compatible_op ow aw)"

(* might have this wrong *)
lemma "((could_have_been_written_by obj v ot) \<and> (is_compatible_txn ot atxn)) \<longrightarrow>
        (\<exists>v0 a r. (AWrite k v0 a v r) \<in> all_awrites atxn)"
  oops


text \<open>Given an observation, we say a version v of key k is recoverable to a transaction t if:
1. There is a unique object with key k in the observation (so THE is well-defined).
2. t is an observed transaction.
3. t could have written v (compatible write exists).
4. t is the only observed transaction that could have written v.\<close>

definition is_recoverable :: "observation \<Rightarrow> key \<Rightarrow> version \<Rightarrow> otxn \<Rightarrow> bool" where
"is_recoverable obs k v ot \<equiv>
  (\<exists>!ob. ob \<in> all_objects obs \<and> key ob = k) \<and>
  ot \<in> all_otxns obs \<and>
  (let obj = (THE ob. ob \<in> all_objects obs \<and> key ob = k) in
    (could_have_been_written_by obj v ot) \<and>
    (\<exists>!t. t \<in> all_otxns obs \<and> could_have_been_written_by obj v t))"

lemma recoverable_unique_obj:
  "is_recoverable obs k v ot \<Longrightarrow> \<exists>!ob. ob \<in> all_objects obs \<and> key ob = k"
  unfolding is_recoverable_def by auto

lemma recoverable_in_obs:
  "is_recoverable obs k v ot \<Longrightarrow> ot \<in> all_otxns obs"
  unfolding is_recoverable_def by auto




end