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


text \<open>The paper requires the observation to be consistent: for each traceable object x,
every committed-read version of x appears in the trace of x_longest. This ensures all
committed versions lie on a single chain, which is needed for the filtered trace to be
a PREFIX (not just subsequence) of the version order.\<close>

definition consistent_observation :: "observation \<Rightarrow> bool" where
"consistent_observation obs \<equiv>
  (\<forall>obj \<in> all_objects obs. is_traceable obj \<longrightarrow>
    (\<forall>v \<in> committed_read_versions obs (key obj).
       v \<in> set (trace_version_list obj (x_longest obs obj))))"

text \<open>The per-object prefix property states that the inferred version list for each object
is a prefix of the actual version order in the history. Proving this from first principles
requires connecting traceability, consistency, cleanness, and version order compatibility --
the paper describes this argument (Section 4.3.2) but omits the formal proof.

We state the per-object property as an explicit assumption below. To discharge it for a
concrete observation, one must show that for each traceable object, the installed versions
in the trace of x_longest form a prefix of the history's version order. This holds when:
1. The history is clean (no aborted reads, intermediate reads, or dirty updates)
2. The observation is consistent (all committed reads lie on a single trace)
3. The version order respects the version graph (from wf_history)\<close>

text \<open>Assembly: given per-object prefix, the global prefix property follows by unfolding
the definitions. This reduces the global property to individual objects.\<close>

lemma inferred_vo_is_prefix_assembly:
  assumes per_object_prefix:
    "\<And>obj. obj \<in> all_objects obs \<Longrightarrow>
      \<exists>vl_h. (KeyVersionOrder (key obj) vl_h) \<in> hvo \<and>
             is_prefix (inferred_version_list obs obj) vl_h"
  shows "is_prefix_version_order (inferred_version_order obs) hvo"
  unfolding is_prefix_version_order_def inferred_version_order_def
  using per_object_prefix by auto


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
          (ORead k (Some xi)) \<in> all_oops ot2)"

definition inferred_rw_depends :: "observation \<Rightarrow> versionOrder \<Rightarrow> otxn \<Rightarrow> otxn \<Rightarrow> bool" where
"inferred_rw_depends obs ivo ot1 ot2 \<equiv>
  (\<exists>k xi xj. (ORead k (Some xi)) \<in> all_oops ot1 \<and>
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
  and ext_write: "\<And>k v. is_recoverable obs k v ot1
    \<Longrightarrow> \<exists>w \<in> ext_awrites (m ot1). key w = k \<and> apost_version w = v"
  and ext_read: "\<And>k v. (ORead k (Some v)) \<in> all_oops ot2
    \<Longrightarrow> \<exists>r \<in> ext_areads (m ot2). key r = k \<and> apre_version r = v"
  shows "wr_depends h (m ot1) (m ot2)"
proof -
  from assms(1) obtain k xi where
    rec1: "is_recoverable obs k xi ot1" and
    read2: "(ORead k (Some xi)) \<in> all_oops ot2"
    unfolding inferred_wr_depends_def by auto
  from ext_write[OF rec1] obtain w1 where
    w1_in: "w1 \<in> ext_awrites (m ot1)" and w1_key: "key w1 = k"
    and w1_post: "apost_version w1 = xi" by auto
  from ext_read[OF read2] obtain r2 where
    r2_in: "r2 \<in> ext_areads (m ot2)" and r2_key: "key r2 = k"
    and r2_pre: "apre_version r2 = xi" by auto
  show ?thesis
    unfolding wr_depends_def
    apply (rule_tac x=w1 in exI)
    apply (rule_tac x=r2 in exI)
    using assms(2,3) w1_in r2_in w1_key r2_key w1_post r2_pre
          aop_post_version aop_pre_version by auto
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
  and ext_read: "\<And>k v. (ORead k (Some v)) \<in> all_oops ot1
    \<Longrightarrow> \<exists>r \<in> ext_areads (m ot1). key r = k \<and> apost_version r = v"
  and ext_write: "\<And>k v. is_recoverable obs k v ot2
    \<Longrightarrow> \<exists>w \<in> ext_awrites (m ot2). key w = k \<and> apost_version w = v"
  shows "rw_depends h (m ot1) (m ot2)"
proof -
  from assms(1) obtain k xi xj where
    read1: "(ORead k (Some xi)) \<in> all_oops ot1" and
    rec2: "is_recoverable obs k xj ot2" and
    inext: "\<exists>kvo \<in> ivo. key kvo = k \<and> is_next_in_key_version_order kvo xi xj"
    unfolding inferred_rw_depends_def by auto
  from ext_read[OF read1] obtain r1 where
    r1_in: "r1 \<in> ext_areads (m ot1)" and r1_key: "key r1 = k"
    and r1_post: "apost_version r1 = xi" by auto
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
    apply (rule_tac x=r1 in exI)
    apply (rule_tac x=w2 in exI)
    using assms(2,3) r1_in w2_in r1_key w2_key r1_post w2_post next_h
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
  and edges_in_obs: "\<And>e. e \<in> set p \<Longrightarrow>
    odep_head e \<in> all_otxns obs \<and> odep_tail e \<in> all_otxns obs"
  shows "cycle (dsg h) (map (map_dep m) p)"
proof -
  from cyc obtain u where
    p_path: "path (idsg obs ivo) u p u" and
    p_dist: "distinct (tl (path_verts (idsg obs ivo) u p))" and
    p_ne: "p \<noteq> []"
    unfolding cycle_def by auto
  let ?p' = "map (map_dep m) p"
  have p'_ne: "?p' \<noteq> []" using p_ne by auto
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
