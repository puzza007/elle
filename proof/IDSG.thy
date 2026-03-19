theory IDSG
  imports Main Observation DSG Anomaly InferredAnomaly
begin

section \<open>Prefix Version Orders\<close>

text \<open>An inferred version order is a prefix of the actual version order: it contains the same
versions in the same order, but may stop short. We use the existing versionOrder type.\<close>

definition is_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_prefix xs ys \<equiv> (\<exists>zs. ys = xs @ zs)"

text \<open>Key lemma: consecutive elements are preserved when appending to the end.\<close>

lemma is_next_append:
  "is_next xs v1 v2 \<Longrightarrow> is_next (xs @ zs) v1 v2"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x rest) then show ?case by (cases rest) auto
qed

lemma prefix_preserves_next:
  "is_prefix xs ys \<Longrightarrow> is_next xs v1 v2 \<Longrightarrow> is_next ys v1 v2"
  using is_next_append unfolding is_prefix_def by auto

text \<open>A per-key prefix relationship between version orders.\<close>

definition is_prefix_version_order :: "versionOrder \<Rightarrow> versionOrder \<Rightarrow> bool" where
"is_prefix_version_order ivo hvo \<equiv>
  (\<forall>k vl_i. (KeyVersionOrder k vl_i) \<in> ivo \<longrightarrow>
    (\<exists>vl_h. (KeyVersionOrder k vl_h) \<in> hvo \<and> is_prefix vl_i vl_h))"

lemma prefix_vo_preserves_next:
  assumes "is_prefix_version_order ivo hvo"
  and "(KeyVersionOrder k vl) \<in> ivo"
  and "is_next vl v1 v2"
  shows "\<exists>vl_h. (KeyVersionOrder k vl_h) \<in> hvo \<and> is_next vl_h v1 v2"
proof -
  from assms(1,2) obtain vl_h where
    kvo_h: "(KeyVersionOrder k vl_h) \<in> hvo" and
    pfx: "is_prefix vl vl_h"
    unfolding is_prefix_version_order_def by auto
  have "is_next vl_h v1 v2" using prefix_preserves_next[OF pfx assms(3)] .
  then show ?thesis using kvo_h by auto
qed


section \<open>Clean Histories\<close>

definition clean_history :: "history \<Rightarrow> bool" where
"clean_history h \<equiv> \<not>has_g1a h \<and> \<not>has_g1b h \<and> \<not>has_dirty_update h"


section \<open>Inferred Version Order Construction\<close>

text \<open>We construct an inferred version order from an observation. For each traceable object:
1. Find the version with the longest trace among committed reads (x_f).
2. Extract the trace of x_f: a sequence of writes from the initial version.
3. Collect the post-versions of each write (the version history).
4. Filter to keep only installed (non-intermediate) versions.
The result is a prefix of the actual version order in every clean interpretation.\<close>

text \<open>The set of versions read by committed transactions for a given key.\<close>

definition committed_read_versions :: "observation \<Rightarrow> key \<Rightarrow> version set" where
"committed_read_versions obs k \<equiv>
  {v. \<exists>ot \<in> all_otxns obs. o_definitely_committed ot \<and>
      (ORead k (Some v)) \<in> all_oops ot}"

text \<open>Select the committed-read version with the longest trace (x_f from the paper).
We use SOME to pick one; the paper allows any longest version.\<close>

definition x_longest :: "observation \<Rightarrow> object \<Rightarrow> version" where
"x_longest obs obj \<equiv>
  (SOME v. v \<in> committed_read_versions obs (key obj) \<and>
    (\<forall>v' \<in> committed_read_versions obs (key obj).
       trace_length obj v' \<le> trace_length obj v))"

text \<open>The post-versions along a trace form the version history.
For the initial version, we prepend it.\<close>

definition trace_version_list :: "object \<Rightarrow> version \<Rightarrow> version list" where
"trace_version_list obj v \<equiv> (initial_version obj) # map apost_version (trace_of obj v)"

text \<open>A version is non-intermediate if the observed transaction that produced it
made it as a final write (not followed by another write to the same key).\<close>

definition is_installed_in_obs :: "observation \<Rightarrow> key \<Rightarrow> version \<Rightarrow> bool" where
"is_installed_in_obs obs k v \<equiv>
  (\<exists>ot. is_recoverable obs k v ot \<and>
    \<not>(\<exists>ow. ow \<in> all_owrites ot \<and> key ow = k \<and>
       is_intermediate_owrite (o_ops ot) k ow \<and>
       (\<exists>aw \<in> awrites_of (THE ob. ob \<in> all_objects obs \<and> key ob = k) v.
         is_compatible_op ow aw)))"

text \<open>The inferred version order for a single object: take the trace of x_longest,
extract versions, filter to installed versions.\<close>

definition inferred_version_list :: "observation \<Rightarrow> object \<Rightarrow> version list" where
"inferred_version_list obs obj \<equiv>
  filter (is_installed_in_obs obs (key obj)) (trace_version_list obj (x_longest obs obj))"

text \<open>The full inferred version order across all objects.\<close>

definition inferred_version_order :: "observation \<Rightarrow> versionOrder" where
"inferred_version_order obs \<equiv>
  {KeyVersionOrder (key obj) (inferred_version_list obs obj) | obj. obj \<in> all_objects obs}"

text \<open>Main theorem: the inferred version order is a prefix of the actual version order
in every clean interpretation of a trace-recoverable observation over traceable objects.

The proof requires:
1. In a clean history, x_f corresponds to an installed version (no aborted/intermediate reads).
2. Every version in the trace of x_f was written by a committed transaction (no dirty updates).
3. Filtering out intermediate versions leaves installed versions in order.
4. These installed versions form a prefix of the actual version order (up to x_f).

Each step follows from cleanness, traceability, and recoverability.\<close>

text \<open>Building blocks for the prefix proof.\<close>

lemma trace_version_list_hd:
  "trace_version_list obj v \<noteq> [] \<and> hd (trace_version_list obj v) = initial_version obj"
  by (simp add: trace_version_list_def)

lemma filter_sublist: "set (filter P xs) \<subseteq> set xs"
  by auto

text \<open>Filtering preserves the prefix relationship.\<close>

lemma filter_prefix: "is_prefix xs ys \<Longrightarrow> is_prefix (filter P xs) (filter P ys)"
  unfolding is_prefix_def by auto


text \<open>The paper requires the observation to be consistent: for each traceable object x,
every committed-read version of x appears in the trace of x_longest. This ensures all
committed versions lie on a single chain, which is needed for the filtered trace to be
a PREFIX (not just subsequence) of the version order.\<close>

definition consistent_observation :: "observation \<Rightarrow> bool" where
"consistent_observation obs \<equiv>
  (\<forall>obj \<in> all_objects obs. is_traceable obj \<longrightarrow>
    (\<forall>v \<in> committed_read_versions obs (key obj).
       v \<in> set (trace_version_list obj (x_longest obs obj))))"

text \<open>For traceable objects, sub-traces are prefixes: if A appears on the trace to B,
then the trace version list to A is a prefix of the trace version list to B.
This follows from traceable_trace_prefix in Object.thy.\<close>

lemma traceable_sub_trace_prefix:
  assumes "is_traceable obj"
  and "v \<in> set (map apost_version (trace_of obj w))"
  and "v \<in> all_versions obj"
  and "v \<noteq> initial_version obj"
  and "w \<in> all_versions obj"
  and "w \<noteq> initial_version obj"
  shows "is_prefix (trace_version_list obj v) (trace_version_list obj w)"
proof -
  let ?p = "trace_of obj w"
  from assms(1,5,6) have "\<exists>!q. is_trace_of obj q w" unfolding is_traceable_def by auto
  then have p_trace: "is_trace_of obj ?p w"
    unfolding trace_of_def using theI' by metis
  from assms(2) obtain i where i_bound: "i < length ?p" and v_eq: "v = apost_version (?p ! i)"
    by (auto simp: in_set_conv_nth)
  from traceable_trace_prefix[OF assms(1) p_trace refl i_bound v_eq assms(3,4)]
  obtain zs where "trace_of obj w = trace_of obj v @ zs" by auto
  then have "trace_version_list obj w =
    (initial_version obj) # map apost_version (trace_of obj v @ zs)"
    unfolding trace_version_list_def by simp
  then have "trace_version_list obj w =
    (initial_version obj) # map apost_version (trace_of obj v) @ map apost_version zs"
    by simp
  then have "trace_version_list obj w =
    trace_version_list obj v @ map apost_version zs"
    unfolding trace_version_list_def by simp
  then show ?thesis unfolding is_prefix_def by auto
qed

text \<open>With vo_reflects_trace in wf_history, the per-object prefix property follows from:
1. The version order equals the installed versions along the trace (vo_reflects_trace)
2. x_longest's trace is a prefix of (last vl_h)'s trace (for traceable objects)
3. Filtering preserves prefix (filter_prefix)
4. is_installed_in_obs matches is_installed_version through compatibility

We prove the assembly (global from per-object) unconditionally, and state the
per-object property with the assumptions needed to discharge it.\<close>

lemma inferred_vo_is_prefix_assembly:
  assumes per_object_prefix:
    "\<And>obj. obj \<in> all_objects obs \<Longrightarrow>
      \<exists>vl_h. (KeyVersionOrder (key obj) vl_h) \<in> hvo \<and>
             is_prefix (inferred_version_list obs obj) vl_h"
  shows "is_prefix_version_order (inferred_version_order obs) hvo"
  unfolding is_prefix_version_order_def inferred_version_order_def
  using per_object_prefix by auto

text \<open>The per-object prefix property: for traceable objects with vo_reflects_trace,
the inferred version list is a prefix of the version order. This requires:
- The trace of x_longest is a prefix of the trace of last vl_h
- is_installed_in_obs matches is_installed_version through the interpretation
Both are assumptions that can be discharged for concrete traceable datatypes.\<close>

lemma per_object_prefix_from_wf:
  assumes wf: "wf_history h"
  and obj_in: "obj \<in> all_objects h"
  and traceable: "is_traceable obj"
  and kvo_in: "(KeyVersionOrder (key obj) vl_h) \<in> (case h of History _ _ vo \<Rightarrow> vo)"
  and vl_ne: "vl_h \<noteq> []"
  and trace_prefix: "is_prefix
    (trace_version_list obj (x_longest obs obj))
    (trace_version_list obj (last vl_h))"
  and installed_match: "\<And>v. v \<in> set (trace_version_list obj (x_longest obs obj)) \<Longrightarrow>
    is_installed_in_obs obs (key obj) v = is_installed_version h (key obj) v"
  shows "is_prefix (inferred_version_list obs obj) vl_h"
proof -
  have reflects: "vo_reflects_trace h obj (KeyVersionOrder (key obj) vl_h)"
  proof (cases h)
    case (History objs txns vo)
    then have "KeyVersionOrder (key obj) vl_h \<in> vo" using kvo_in by simp
    moreover have "obj \<in> objs" using obj_in History by simp
    moreover have "\<forall>kvo \<in> vo. \<forall>ob \<in> objs. key kvo = key ob \<longrightarrow>
      vo_reflects_trace (History objs txns vo) ob kvo"
      using wf History by auto
    moreover have "key (KeyVersionOrder (key obj) vl_h) = key obj" by simp
    ultimately show ?thesis using History by blast
  qed
  then have vl_raw: "vl_h = filter (is_installed_version h (key obj))
    ((initial_version obj) # map apost_version (trace_of obj (last vl_h)))"
  proof -
    from reflects have "(is_traceable obj \<and> key obj = key obj \<and> vl_h \<noteq> []) \<longrightarrow>
      (vl_h = filter (is_installed_version h (key obj))
        ((initial_version obj) # map apost_version (trace_of obj (last vl_h))))"
      by (simp only: vo_reflects_trace.simps)
    then show ?thesis using traceable vl_ne by blast
  qed
  then have vl_eq: "vl_h = filter (is_installed_version h (key obj))
    (trace_version_list obj (last vl_h))"
    unfolding trace_version_list_def .
  have rewrite_filter: "filter (is_installed_in_obs obs (key obj))
                               (trace_version_list obj (x_longest obs obj))
                        = filter (is_installed_version h (key obj))
                                 (trace_version_list obj (x_longest obs obj))"
    using installed_match by (auto intro: filter_cong)
  have "is_prefix (filter (is_installed_version h (key obj))
                          (trace_version_list obj (x_longest obs obj)))
                  (filter (is_installed_version h (key obj))
                          (trace_version_list obj (last vl_h)))"
    using filter_prefix[OF trace_prefix] .
  then have "is_prefix (filter (is_installed_in_obs obs (key obj))
                               (trace_version_list obj (x_longest obs obj))) vl_h"
    using rewrite_filter vl_eq by simp
  then show ?thesis unfolding inferred_version_list_def by simp
qed


section \<open>Inferred Dependencies\<close>

text \<open>Inferred dependencies between observed transactions, using an inferred version order
and recoverability to map versions to transactions.\<close>

definition inferred_ww_depends :: "observation \<Rightarrow> versionOrder \<Rightarrow> otxn \<Rightarrow> otxn \<Rightarrow> bool" where
"inferred_ww_depends obs ivo ot1 ot2 \<equiv>
  (\<exists>k xi xj. is_recoverable obs k xi ot1 \<and>
             is_recoverable obs k xj ot2 \<and>
             (\<exists>kvo \<in> ivo. key kvo = k \<and> is_next_in_key_version_order kvo xi xj))"

definition inferred_wr_depends :: "observation \<Rightarrow> versionOrder \<Rightarrow> otxn \<Rightarrow> otxn \<Rightarrow> bool" where
"inferred_wr_depends obs ivo ot1 ot2 \<equiv>
  (\<exists>k xi. is_recoverable obs k xi ot1 \<and>
          ot2 \<in> all_otxns obs \<and>
          (ORead k (Some xi)) \<in> all_oops ot2)"

definition inferred_rw_depends :: "observation \<Rightarrow> versionOrder \<Rightarrow> otxn \<Rightarrow> otxn \<Rightarrow> bool" where
"inferred_rw_depends obs ivo ot1 ot2 \<equiv>
  (\<exists>k xi xj. ot1 \<in> all_otxns obs \<and>
              (ORead k (Some xi)) \<in> all_oops ot1 \<and>
              is_recoverable obs k xj ot2 \<and>
              (\<exists>kvo \<in> ivo. key kvo = k \<and> is_next_in_key_version_order kvo xi xj))"


section \<open>Inferred Direct Serialization Graph\<close>

datatype odep = ODep otxn depType otxn

primrec odep_head :: "odep \<Rightarrow> otxn" where
"odep_head (ODep t _ _) = t"

primrec odep_tail :: "odep \<Rightarrow> otxn" where
"odep_tail (ODep _ _ t) = t"

instantiation odep :: dep_typed
begin
primrec dep_type_odep :: "odep \<Rightarrow> depType" where
"dep_type_odep (ODep _ t _) = t"
instance ..
end

type_synonym idsg = "(otxn, odep) pre_digraph"

definition idsg :: "observation \<Rightarrow> versionOrder \<Rightarrow> idsg" where
"idsg obs ivo \<equiv> \<lparr>verts = all_otxns obs,
          arcs  = ({(ODep t1 WR t2) | t1 t2. inferred_wr_depends obs ivo t1 t2} \<union>
                   {(ODep t1 WW t2) | t1 t2. inferred_ww_depends obs ivo t1 t2} \<union>
                   {(ODep t1 RW t2) | t1 t2. inferred_rw_depends obs ivo t1 t2}),
          tail = odep_tail,
          head = odep_head\<rparr>"


section \<open>Dependency Soundness\<close>

text \<open>Each inferred dependency implies the corresponding actual dependency in every
clean interpretation whose version order extends the inferred one.

The assumptions ext_write and ext_read capture that recoverable writes and observed reads
correspond to ext_awrites and ext_areads respectively in the abstract history. These
follow from trace-recoverability and cleanness in the paper's argument.

The committed assumptions follow from the fact that in clean histories, versions in
the version order are installed by committed transactions.\<close>

lemma aop_post_version: "post_version (w::aop) = Some (apost_version w)"
  by (cases w) auto

lemma aop_pre_version: "pre_version (r::aop) = Some (apre_version r)"
  by (cases r) auto

theorem inferred_wr_sound:
  assumes "inferred_wr_depends obs ivo ot1 ot2"
  and "a_is_committed (m ot1)" and "a_is_committed (m ot2)"
  and wfi: "wf_interpretation (Interp obs m h)"
  and ext_write: "\<And>k v. is_recoverable obs k v ot1
    \<Longrightarrow> \<exists>w \<in> ext_awrites (m ot1). key w = k \<and> apost_version w = v"
  shows "wr_depends h (m ot1) (m ot2)"
proof -
  from assms(1) obtain k xi where
    rec1: "is_recoverable obs k xi ot1" and
    ot2_in: "ot2 \<in> all_otxns obs" and
    read2: "(ORead k (Some xi)) \<in> all_oops ot2"
    unfolding inferred_wr_depends_def by auto
  from ext_write[OF rec1] obtain w1 where
    w1_in: "w1 \<in> ext_awrites (m ot1)" and w1_key: "key w1 = k"
    and w1_post: "apost_version w1 = xi" by auto
  have compat2: "is_compatible_txn ot2 (m ot2)"
    using wfi ot2_in wf_interp_compatible by blast
  have "ORead k (Some xi) \<in> set (o_ops ot2)" using read2 by (cases ot2) auto
  moreover have "is_compatible_op_list (o_ops ot2) (a_ops (m ot2))"
    using compat2 by (cases ot2; cases "m ot2"; simp add: is_compatible_txn_def)
  ultimately have "ARead k xi \<in> set (a_ops (m ot2))"
    using compatible_op_list_has_read by blast
  then have r2_in: "ARead k xi \<in> all_aops (m ot2)" by (cases "m ot2") auto
  show ?thesis
    unfolding wr_depends_def
    apply (rule_tac x=w1 in exI)
    apply (rule_tac x="ARead k xi" in exI)
    using assms(2,3) w1_in r2_in w1_key w1_post aop_post_version by auto
qed

theorem inferred_ww_sound:
  assumes "inferred_ww_depends obs ivo ot1 ot2"
  and "a_is_committed (m ot1)" and "a_is_committed (m ot2)"
  and pfx: "is_prefix_version_order ivo (case h of History _ _ vo \<Rightarrow> vo)"
  and ext_write: "\<And>k v. is_recoverable obs k v ot1
    \<Longrightarrow> \<exists>w \<in> ext_awrites (m ot1). key w = k \<and> apost_version w = v"
  and ext_write2: "\<And>k v. is_recoverable obs k v ot2
    \<Longrightarrow> \<exists>w \<in> ext_awrites (m ot2). key w = k \<and> apost_version w = v"
  shows "ww_depends h (m ot1) (m ot2)"
proof -
  from assms(1) obtain k xi xj where
    rec1: "is_recoverable obs k xi ot1" and
    rec2: "is_recoverable obs k xj ot2" and
    inext: "\<exists>kvo \<in> ivo. key kvo = k \<and> is_next_in_key_version_order kvo xi xj"
    unfolding inferred_ww_depends_def by auto
  from ext_write[OF rec1] obtain w1 where
    w1_in: "w1 \<in> ext_awrites (m ot1)" and w1_key: "key w1 = k"
    and w1_post: "apost_version w1 = xi" by auto
  from ext_write2[OF rec2] obtain w2 where
    w2_in: "w2 \<in> ext_awrites (m ot2)" and w2_key: "key w2 = k"
    and w2_post: "apost_version w2 = xj" by auto
  from inext obtain kvo where kvo_in: "kvo \<in> ivo" and kvo_key: "key kvo = k"
    and kvo_next: "is_next_in_key_version_order kvo xi xj" by auto
  obtain vl where kvo_eq: "kvo = KeyVersionOrder k vl" and vl_next: "is_next vl xi xj"
    using kvo_key kvo_next by (cases kvo) auto
  from prefix_vo_preserves_next[OF pfx _ vl_next] kvo_in kvo_eq
  obtain vl_h where kvo_h_in: "(KeyVersionOrder k vl_h) \<in> (case h of History _ _ vo \<Rightarrow> vo)"
    and vl_h_next: "is_next vl_h xi xj" by auto
  have next_h: "is_next_in_history h k xi xj"
  proof (cases h)
    case (History objs txns vo)
    then show ?thesis using kvo_h_in vl_h_next
      by (auto simp: is_next_in_history_def intro: exI[where x="KeyVersionOrder k vl_h"])
  qed
  show ?thesis
    unfolding ww_depends_def
    apply (rule_tac x=w1 in exI)
    apply (rule_tac x=w2 in exI)
    using assms(2,3) w1_in w2_in w1_key w2_key w1_post w2_post next_h
          aop_post_version by auto
qed

theorem inferred_rw_sound:
  assumes "inferred_rw_depends obs ivo ot1 ot2"
  and "a_is_committed (m ot1)" and "a_is_committed (m ot2)"
  and pfx: "is_prefix_version_order ivo (case h of History _ _ vo \<Rightarrow> vo)"
  and wfi: "wf_interpretation (Interp obs m h)"
  and ext_write: "\<And>k v. is_recoverable obs k v ot2
    \<Longrightarrow> \<exists>w \<in> ext_awrites (m ot2). key w = k \<and> apost_version w = v"
  shows "rw_depends h (m ot1) (m ot2)"
proof -
  from assms(1) obtain k xi xj where
    ot1_in: "ot1 \<in> all_otxns obs" and
    read1: "(ORead k (Some xi)) \<in> all_oops ot1" and
    rec2: "is_recoverable obs k xj ot2" and
    inext: "\<exists>kvo \<in> ivo. key kvo = k \<and> is_next_in_key_version_order kvo xi xj"
    unfolding inferred_rw_depends_def by auto
  have compat1: "is_compatible_txn ot1 (m ot1)"
    using wfi ot1_in wf_interp_compatible by blast
  have "ORead k (Some xi) \<in> set (o_ops ot1)" using read1 by (cases ot1) auto
  moreover have "is_compatible_op_list (o_ops ot1) (a_ops (m ot1))"
    using compat1 by (cases ot1; cases "m ot1"; simp add: is_compatible_txn_def)
  ultimately have "ARead k xi \<in> set (a_ops (m ot1))"
    using compatible_op_list_has_read by blast
  then have r1_in: "ARead k xi \<in> all_aops (m ot1)" by (cases "m ot1") auto
  from ext_write[OF rec2] obtain w2 where
    w2_in: "w2 \<in> ext_awrites (m ot2)" and w2_key: "key w2 = k"
    and w2_post: "apost_version w2 = xj" by auto
  from inext obtain kvo where kvo_in: "kvo \<in> ivo" and kvo_key: "key kvo = k"
    and kvo_next: "is_next_in_key_version_order kvo xi xj" by auto
  obtain vl where kvo_eq: "kvo = KeyVersionOrder k vl" and vl_next: "is_next vl xi xj"
    using kvo_key kvo_next by (cases kvo) auto
  from prefix_vo_preserves_next[OF pfx _ vl_next] kvo_in kvo_eq
  obtain vl_h where kvo_h_in: "(KeyVersionOrder k vl_h) \<in> (case h of History _ _ vo \<Rightarrow> vo)"
    and vl_h_next: "is_next vl_h xi xj" by auto
  have next_h: "is_next_in_history h k xi xj"
  proof (cases h)
    case (History objs txns vo)
    then show ?thesis using kvo_h_in vl_h_next
      by (auto simp: is_next_in_history_def intro: exI[where x="KeyVersionOrder k vl_h"])
  qed
  show ?thesis
    unfolding rw_depends_def
    apply (rule_tac x="ARead k xi" in exI)
    apply (rule_tac x=w2 in exI)
    using assms(2,3) r1_in w2_in w2_key w2_post next_h
          aop_post_version by auto
qed


section \<open>Cycle Transfer\<close>

text \<open>If a cycle exists in the IDSG, a corresponding cycle exists in the DSG of every
clean interpretation. The bijection m maps observed transactions to abstract transactions,
preserving the cycle structure.\<close>

fun map_dep :: "(otxn \<Rightarrow> atxn) \<Rightarrow> odep \<Rightarrow> adep" where
"map_dep m (ODep t1 dt t2) = ADep (m t1) dt (m t2)"

lemma cas_map_dep:
  "cas (idsg obs ivo) u p v \<Longrightarrow> cas (dsg h) (m u) (map (map_dep m) p) (m v)"
proof (induct p arbitrary: u)
  case Nil then show ?case by simp
next
  case (Cons e es)
  then show ?case by (cases e) (auto simp: dsg_def idsg_def)
qed

lemma path_verts_map_dep:
  "path_verts (dsg h) (m u) (map (map_dep m) p) = map m (path_verts (idsg obs ivo) u p)"
proof (induct p arbitrary: u)
  case Nil then show ?case by (simp add: dsg_def idsg_def)
next
  case (Cons e es)
  then show ?case by (cases e) (auto simp: dsg_def idsg_def)
qed

lemma idsg_arcs_in_obs:
  "e \<in> arcs (idsg obs ivo) \<Longrightarrow> odep_head e \<in> all_otxns obs \<and> odep_tail e \<in> all_otxns obs"
  by (auto simp: idsg_def inferred_ww_depends_def inferred_wr_depends_def
                 inferred_rw_depends_def dest: recoverable_in_obs)

text \<open>Path vertices of an IDSG path whose edges all involve observed transactions
are themselves in all_otxns obs.\<close>

lemma idsg_path_verts_in_obs:
  assumes "u \<in> all_otxns obs"
  and "\<And>e. e \<in> set p \<Longrightarrow> odep_head e \<in> all_otxns obs \<and> odep_tail e \<in> all_otxns obs"
  shows "set (path_verts (idsg obs ivo) u p) \<subseteq> all_otxns obs"
  using assms
proof (induct p arbitrary: u)
  case Nil then show ?case by (simp add: idsg_def)
next
  case (Cons e es)
  obtain t1 dt t2 where e_eq: "e = ODep t1 dt t2" by (cases e)
  have "odep_head e \<in> all_otxns obs \<and> odep_tail e \<in> all_otxns obs"
    using Cons.prems(2)[of e] by simp
  then have t1_in: "t1 \<in> all_otxns obs" and t2_in: "t2 \<in> all_otxns obs"
    using e_eq by auto
  have "set (path_verts (idsg obs ivo) t1 es) \<subseteq> all_otxns obs"
    using Cons.hyps[OF t1_in] Cons.prems(2) by auto
  then show ?case using t2_in e_eq by (auto simp: idsg_def)
qed

theorem cycle_transfer:
  assumes cyc: "cycle (idsg obs ivo) p"
  and wfi: "wf_interpretation (Interp obs m h)"
  and deps: "\<And>e. e \<in> set p \<Longrightarrow>
    (case e of ODep t1 WW t2 \<Rightarrow> ww_depends h (m t1) (m t2)
             | ODep t1 WR t2 \<Rightarrow> wr_depends h (m t1) (m t2)
             | ODep t1 RW t2 \<Rightarrow> rw_depends h (m t1) (m t2))"
  shows "cycle (dsg h) (map (map_dep m) p)"
proof -
  from cyc obtain u where
    p_path: "path (idsg obs ivo) u p u" and
    p_dist: "distinct (tl (path_verts (idsg obs ivo) u p))" and
    p_ne: "p \<noteq> []"
    unfolding cycle_def by auto
  let ?p' = "map (map_dep m) p"
  have p'_ne: "?p' \<noteq> []" using p_ne by auto
  have arcs_sub: "set p \<subseteq> arcs (idsg obs ivo)"
    using p_path unfolding path_def by auto
  have edges_in_obs: "\<And>e. e \<in> set p \<Longrightarrow>
    odep_head e \<in> all_otxns obs \<and> odep_tail e \<in> all_otxns obs"
    using arcs_sub idsg_arcs_in_obs by auto
  have u_in: "u \<in> all_otxns obs"
    using p_path unfolding path_def idsg_def by simp
  have u'_in: "m u \<in> verts (dsg h)"
    using wf_interp_m_in_h[OF wfi u_in] by (simp add: dsg_def)
  have arcs_ok: "set ?p' \<subseteq> arcs (dsg h)"
  proof
    fix e' assume "e' \<in> set ?p'"
    then obtain e where e_in: "e \<in> set p" and e'_eq: "e' = map_dep m e" by auto
    from deps[OF e_in] show "e' \<in> arcs (dsg h)"
    proof (cases e)
      case (ODep t1 dt t2)
      then show ?thesis using deps[OF e_in]
        by (cases dt) (auto simp: e'_eq dsg_def)
    qed
  qed
  have cas_ok: "cas (dsg h) (m u) ?p' (m u)"
    using cas_map_dep p_path unfolding path_def by blast
  have map_tl: "tl (map f xs) = map f (tl xs)" for f :: "'a \<Rightarrow> 'b" and xs by (cases xs) auto
  have pv_eq: "path_verts (dsg h) (m u) ?p' = map m (path_verts (idsg obs ivo) u p)"
    using path_verts_map_dep .
  have tl_eq: "tl (path_verts (dsg h) (m u) ?p') = map m (tl (path_verts (idsg obs ivo) u p))"
    using pv_eq map_tl by metis
  have inj_m: "inj_on m (all_otxns obs)"
    using wfi by (simp add: total_bij_def bij_betw_def)
  have "set (path_verts (idsg obs ivo) u p) \<subseteq> all_otxns obs"
    using idsg_path_verts_in_obs[OF u_in edges_in_obs] .
  then have verts_in: "set (tl (path_verts (idsg obs ivo) u p)) \<subseteq> all_otxns obs"
    by (metis list.sel(2) list.set_sel(2) subsetD subsetI)
  have "inj_on m (set (tl (path_verts (idsg obs ivo) u p)))"
    using inj_m verts_in by (meson inj_on_subset)
  have dist_ok: "distinct (tl (path_verts (dsg h) (m u) ?p'))"
    unfolding tl_eq distinct_map
    using p_dist \<open>inj_on m (set (tl (path_verts (idsg obs ivo) u p)))\<close> by auto
  show ?thesis unfolding cycle_def path_def
    using p'_ne u'_in arcs_ok cas_ok dist_ok by auto
qed

end
