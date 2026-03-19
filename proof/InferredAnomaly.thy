theory InferredAnomaly
  imports Main Observation Anomaly
begin

section \<open>Bridge Lemmas for Compatibility\<close>

lemma compatible_read_aread:
  "is_compatible_op (ORead k (Some v)) aop \<Longrightarrow> aop = ARead k v"
  by (cases aop) (auto simp: is_compatible_op_def)

lemma compatible_op_list_member:
  "is_compatible_op_list oos aos \<Longrightarrow> oop \<in> set oos \<Longrightarrow>
   \<exists>aop \<in> set aos. is_compatible_op oop aop"
  by (induct oos aos rule: is_compatible_op_list.induct) auto

lemma compatible_op_list_has_read:
  "is_compatible_op_list oos aos \<Longrightarrow> ORead k (Some v) \<in> set oos \<Longrightarrow>
   ARead k v \<in> set aos"
  using compatible_op_list_member compatible_read_aread by fastforce

lemma compatible_committed_state:
  "is_compatible_txn ot atx \<Longrightarrow> o_is_committed ot = Some b \<Longrightarrow> a_is_committed atx = b"
  by (cases ot; cases atx; auto simp: is_compatible_txn_def)

lemma wf_interp_compatible:
  "wf_interpretation (Interp obs m h) \<Longrightarrow> ot \<in> all_otxns obs \<Longrightarrow>
   is_compatible_txn ot (m ot)"
  by (simp add: is_compatible_observation_def)

lemma wf_interp_m_in_h:
  "wf_interpretation (Interp obs m h) \<Longrightarrow> ot \<in> all_otxns obs \<Longrightarrow> m ot \<in> all_atxns h"
proof -
  assume "wf_interpretation (Interp obs m h)" and "ot \<in> all_otxns obs"
  then have "m ` (all_otxns obs) = all_atxns h"
    by (simp add: total_bij_def bij_betw_def)
  with \<open>ot \<in> all_otxns obs\<close> show "m ot \<in> all_atxns h" by blast
qed

lemma compatible_write_definite_post:
  "is_compatible_op ow aw \<Longrightarrow> post_version ow = Some v \<Longrightarrow> apost_version aw = v"
  by (cases ow; cases aw; auto simp: is_compatible_op_def)

lemma compatible_write_definite_pre:
  "is_compatible_op ow aw \<Longrightarrow> pre_version ow = Some v \<Longrightarrow> apre_version aw = v"
  by (cases ow; cases aw; auto simp: is_compatible_op_def)

section \<open>Inferred G1a\<close>

definition has_ig1a :: "observation \<Rightarrow> bool" where
"has_ig1a obs \<equiv> (\<exists>t1 t2 k v. t1 \<in> all_otxns obs \<and>
                              t2 \<in> all_otxns obs \<and>
                              o_is_committed t1 = Some False \<and>
                              o_is_committed t2 = Some True \<and>
                              is_recoverable obs k v t1 \<and>
                              (ORead k (Some v)) \<in> (all_oops t2))"

theorem ig1a_sound:
  assumes ig: "has_ig1a obs"
  and wf: "wf_interpretation (Interp obs m h)"
  and write_definite: "\<And>ot k v obj ow aw.
    \<lbrakk>ot \<in> all_otxns obs; is_recoverable obs k v ot;
     obj = (THE ob. ob \<in> all_objects obs \<and> key ob = k);
     ow \<in> all_owrites ot; aw \<in> awrites_of obj v;
     is_compatible_op ow aw\<rbrakk> \<Longrightarrow> post_version ow \<noteq> None"
  and unique_objects: "\<And>k v ot. \<lbrakk>ot \<in> all_otxns obs; is_recoverable obs k v ot\<rbrakk>
    \<Longrightarrow> \<exists>!ob. ob \<in> all_objects obs \<and> key ob = k"
  shows "has_g1a h"
proof -
  from ig obtain ot1 ot2 k v where
    ot1_in: "ot1 \<in> all_otxns obs" and
    ot2_in: "ot2 \<in> all_otxns obs" and
    ot1_aborted: "o_is_committed ot1 = Some False" and
    ot2_committed: "o_is_committed ot2 = Some True" and
    recoverable: "is_recoverable obs k v ot1" and
    read_in_ot2: "(ORead k (Some v)) \<in> all_oops ot2"
    unfolding has_ig1a_def by auto
  let ?at1 = "m ot1"
  let ?at2 = "m ot2"
  have at1_in: "?at1 \<in> all_atxns h" using wf ot1_in wf_interp_m_in_h by blast
  have at2_in: "?at2 \<in> all_atxns h" using wf ot2_in wf_interp_m_in_h by blast
  have compat1: "is_compatible_txn ot1 ?at1" using wf ot1_in wf_interp_compatible by blast
  have compat2: "is_compatible_txn ot2 ?at2" using wf ot2_in wf_interp_compatible by blast
  have at1_aborted: "\<not>(a_is_committed ?at1)"
    using compat1 ot1_aborted compatible_committed_state by fastforce
  have at2_committed: "a_is_committed ?at2"
    using compat2 ot2_committed compatible_committed_state by fastforce
  have read_in_at2: "ARead k v \<in> all_aops ?at2"
  proof -
    have "ORead k (Some v) \<in> set (o_ops ot2)" using read_in_ot2 by (cases ot2) auto
    moreover have "is_compatible_op_list (o_ops ot2) (a_ops ?at2)"
      using compat2 by (cases ot2; cases ?at2; simp add: is_compatible_txn_def)
    ultimately have "ARead k v \<in> set (a_ops ?at2)"
      using compatible_op_list_has_read by blast
    then show ?thesis by (cases ?at2) auto
  qed
  have write_in_at1: "\<exists>v1 a r. AWrite k v1 a v r \<in> all_aops ?at1"
  proof -
    let ?obj = "THE ob. ob \<in> all_objects obs \<and> key ob = k"
    from recoverable obtain aw ow where
      aw_in: "aw \<in> awrites_of ?obj v" and
      ow_in: "ow \<in> all_owrites ot1" and
      ow_aw_compat: "is_compatible_op ow aw"
      unfolding is_recoverable_def could_have_been_written_by_def by (auto simp: Let_def)
    have ow_in_ops: "ow \<in> set (o_ops ot1)"
      using ow_in by (cases ot1; auto simp: all_owrites_def)
    have "is_compatible_op_list (o_ops ot1) (a_ops ?at1)"
      using compat1 by (cases ot1; cases ?at1; simp add: is_compatible_txn_def)
    then obtain aw' where aw'_in: "aw' \<in> set (a_ops ?at1)"
      and ow_aw'_compat: "is_compatible_op ow aw'"
      using compatible_op_list_member ow_in_ops by blast
    have "post_version ow \<noteq> None"
      using write_definite[OF ot1_in recoverable refl ow_in aw_in ow_aw_compat] by simp
    then obtain pv where pv: "post_version ow = Some pv" by auto
    have "apost_version aw = pv"
      using ow_aw_compat pv compatible_write_definite_post by blast
    moreover have "apost_version aw' = pv"
      using ow_aw'_compat pv compatible_write_definite_post by blast
    moreover have "apost_version aw = v"
      using aw_in by (auto simp: awrites_of_def all_awrites_def)
    ultimately have post_v: "apost_version aw' = v" by simp
    have "key ow = key aw'" using ow_aw'_compat compatible_same_key by blast
    moreover have "key ow = key aw" using ow_aw_compat compatible_same_key by blast
    ultimately have keys_eq: "key aw' = key aw" by simp
    text \<open>key aw = k: from wf_object_arc_keys (arcs use the object's key).\<close>
    have aw_in_obj: "aw \<in> all_aops ?obj"
      using aw_in by (auto simp: awrites_of_def all_awrites_def)
    have obs_eq: "all_objects obs = all_objects h"
      using wf by (simp add: is_compatible_observation_def)
    have obj_wf: "\<forall>obj \<in> all_objects h. wf_object obj"
      using wf by (cases h; auto)
    have obj_unique: "\<exists>!ob. ob \<in> all_objects obs \<and> key ob = k"
      using unique_objects[OF ot1_in recoverable] by simp
    then have obj_props: "?obj \<in> all_objects obs \<and> key ?obj = k"
      by (rule theI')
    have aw_key: "key aw = k"
    proof -
      have "?obj \<in> all_objects h" using obj_props obs_eq by simp
      then have "wf_object ?obj" using obj_wf by auto
      then have "wf_object_arc_keys ?obj" unfolding wf_object_def by simp
      then have "key aw = key ?obj"
        using aw_in_obj unfolding wf_object_arc_keys_def by auto
      then show ?thesis using obj_props by simp
    qed
    have aw'_key: "key aw' = k" using keys_eq aw_key by simp
    have "op_type ow = Write" using ow_in by (cases ot1; auto simp: all_owrites_def)
    then have aw'_type: "op_type aw' = Write"
      using ow_aw'_compat compatible_same_type by fastforce
    from aw'_type aw'_key post_v obtain v1 a r where "aw' = AWrite k v1 a v r"
      by (cases aw') auto
    moreover have "aw' \<in> all_aops ?at1" using aw'_in by (cases ?at1) auto
    ultimately show ?thesis by blast
  qed
  from write_in_at1 obtain v1 a r where "AWrite k v1 a v r \<in> all_aops ?at1" by blast
  then show ?thesis
    unfolding has_g1a_def
    using at1_in at2_in at1_aborted at2_committed read_in_at2 by blast
qed


section \<open>Inferred G1b (Intermediate Reads)\<close>

text \<open>Position-wise compatibility: compatible op lists are element-wise compatible.\<close>

lemma compatible_op_list_nth:
  "is_compatible_op_list oos aos \<Longrightarrow> i < length oos \<Longrightarrow>
   i < length aos \<and> is_compatible_op (oos ! i) (aos ! i)"
proof (induct oos aos arbitrary: i rule: is_compatible_op_list.induct)
  case 1 then show ?case by simp
next
  case 2 then show ?case by simp
next
  case 3 then show ?case by simp
next
  case (4 o1 os a1 as)
  then show ?case by (cases i) auto
qed

text \<open>An intermediate observed write maps to an intermediate abstract write.\<close>

definition is_intermediate_owrite :: "oop list \<Rightarrow> key \<Rightarrow> oop \<Rightarrow> bool" where
"is_intermediate_owrite ops k w \<equiv>
  (\<exists>i j. i < length ops \<and> j < length ops \<and> i < j \<and>
         ops ! i = w \<and> op_type (ops ! j) = Write \<and> key (ops ! j) = k)"

lemma intermediate_write_compatible:
  assumes compat: "is_compatible_op_list oos aos"
  and inter: "is_intermediate_owrite oos k ow"
  shows "\<exists>i. i < length aos \<and> is_compatible_op ow (aos ! i) \<and>
             is_intermediate_awrite aos k (aos ! i)"
proof -
  from inter obtain i j where
    ib: "i < length oos" and jb: "j < length oos" and ij: "i < j" and
    ow_at_i: "oos ! i = ow" and jw: "op_type (oos ! j) = Write" and jk: "key (oos ! j) = k"
    unfolding is_intermediate_owrite_def by auto
  have len: "length oos = length aos" using compat is_compatible_op_list_size by blast
  have ia: "i < length aos" using ib len by simp
  have ja: "j < length aos" using jb len by simp
  have ci: "is_compatible_op (oos ! i) (aos ! i)"
    using compatible_op_list_nth[OF compat ib] by simp
  have cj: "is_compatible_op (oos ! j) (aos ! j)"
    using compatible_op_list_nth[OF compat jb] by simp
  have jwA: "op_type (aos ! j) = Write" using cj jw compatible_same_type by fastforce
  have jkA: "key (aos ! j) = k" using cj jk compatible_same_key by fastforce
  have "is_intermediate_awrite aos k (aos ! i)"
    unfolding is_intermediate_awrite_def
    apply (rule_tac x=i in exI)
    apply (rule_tac x=j in exI)
    using ia ja ij jwA jkA by auto
  then show ?thesis using ia ci ow_at_i by auto
qed

text \<open>Inferred G1b: a committed observed transaction has an intermediate write producing v,
and another committed observed transaction reads v.\<close>

definition has_ig1b :: "observation \<Rightarrow> bool" where
"has_ig1b obs \<equiv> (\<exists>t1 t2 k v ow. t1 \<in> all_otxns obs \<and>
                              t2 \<in> all_otxns obs \<and>
                              o_is_committed t1 = Some True \<and>
                              o_is_committed t2 = Some True \<and>
                              is_recoverable obs k v t1 \<and>
                              ow \<in> all_owrites t1 \<and>
                              (\<exists>aw \<in> awrites_of
                                (THE ob. ob \<in> all_objects obs \<and> key ob = k) v.
                                is_compatible_op ow aw) \<and>
                              is_intermediate_owrite (o_ops t1) k ow \<and>
                              (ORead k (Some v)) \<in> (all_oops t2))"

text \<open>G1b soundness. The proof mirrors G1a but additionally shows the abstract write is
intermediate, using the position-wise compatibility bridge.\<close>

theorem ig1b_sound:
  assumes ig: "has_ig1b obs"
  and wf: "wf_interpretation (Interp obs m h)"
  and write_definite: "\<And>ot k v obj ow aw.
    \<lbrakk>ot \<in> all_otxns obs; is_recoverable obs k v ot;
     obj = (THE ob. ob \<in> all_objects obs \<and> key ob = k);
     ow \<in> all_owrites ot; aw \<in> awrites_of obj v;
     is_compatible_op ow aw\<rbrakk> \<Longrightarrow> post_version ow \<noteq> None"
  and unique_objects: "\<And>k v ot. \<lbrakk>ot \<in> all_otxns obs; is_recoverable obs k v ot\<rbrakk>
    \<Longrightarrow> \<exists>!ob. ob \<in> all_objects obs \<and> key ob = k"
  shows "has_g1b h"
proof -
  from ig obtain ot1 ot2 k v ow where
    ot1_in: "ot1 \<in> all_otxns obs" and ot2_in: "ot2 \<in> all_otxns obs" and
    ot1_comm: "o_is_committed ot1 = Some True" and
    ot2_comm: "o_is_committed ot2 = Some True" and
    recoverable: "is_recoverable obs k v ot1" and
    ow_in: "ow \<in> all_owrites ot1" and
    ow_compat_aw: "\<exists>aw \<in> awrites_of (THE ob. ob \<in> all_objects obs \<and> key ob = k) v.
                    is_compatible_op ow aw" and
    ow_inter: "is_intermediate_owrite (o_ops ot1) k ow" and
    read_in_ot2: "(ORead k (Some v)) \<in> all_oops ot2"
    unfolding has_ig1b_def by blast
  let ?at1 = "m ot1" and ?at2 = "m ot2"
  have at1_in: "?at1 \<in> all_atxns h" using wf ot1_in wf_interp_m_in_h by blast
  have at2_in: "?at2 \<in> all_atxns h" using wf ot2_in wf_interp_m_in_h by blast
  have compat1: "is_compatible_txn ot1 ?at1" using wf ot1_in wf_interp_compatible by blast
  have compat2: "is_compatible_txn ot2 ?at2" using wf ot2_in wf_interp_compatible by blast
  have at1_comm: "a_is_committed ?at1"
    using compat1 ot1_comm compatible_committed_state by fastforce
  have at2_comm: "a_is_committed ?at2"
    using compat2 ot2_comm compatible_committed_state by fastforce
  text \<open>at2 reads v.\<close>
  have read_in_at2: "ARead k v \<in> all_aops ?at2"
  proof -
    have "ORead k (Some v) \<in> set (o_ops ot2)" using read_in_ot2 by (cases ot2) auto
    moreover have "is_compatible_op_list (o_ops ot2) (a_ops ?at2)"
      using compat2 by (cases ot2; cases ?at2; simp add: is_compatible_txn_def)
    ultimately have "ARead k v \<in> set (a_ops ?at2)"
      using compatible_op_list_has_read by blast
    then show ?thesis by (cases ?at2) auto
  qed
  text \<open>at1 has an intermediate write producing v. Use the bridge lemma.\<close>
  have compat_list1: "is_compatible_op_list (o_ops ot1) (a_ops ?at1)"
    using compat1 by (cases ot1; cases ?at1; simp add: is_compatible_txn_def)
  from intermediate_write_compatible[OF compat_list1 ow_inter]
  obtain i where ia: "i < length (a_ops ?at1)" and
    ci: "is_compatible_op ow (a_ops ?at1 ! i)" and
    inter_a: "is_intermediate_awrite (a_ops ?at1) k (a_ops ?at1 ! i)" by auto
  text \<open>The abstract op at position i produces v (same argument as ig1a).\<close>
  let ?obj = "THE ob. ob \<in> all_objects obs \<and> key ob = k"
  from ow_compat_aw obtain aw where
    aw_in: "aw \<in> awrites_of ?obj v" and ow_aw: "is_compatible_op ow aw" by auto
  have "post_version ow \<noteq> None"
    using write_definite[OF ot1_in recoverable refl ow_in aw_in ow_aw] by simp
  then obtain pv where pv: "post_version ow = Some pv" by auto
  have "apost_version aw = pv" using ow_aw pv compatible_write_definite_post by blast
  moreover have "apost_version (a_ops ?at1 ! i) = pv"
    using ci pv compatible_write_definite_post by blast
  moreover have "apost_version aw = v"
    using aw_in by (auto simp: awrites_of_def all_awrites_def)
  ultimately have post_v: "apost_version (a_ops ?at1 ! i) = v" by simp
  have obs_eq: "all_objects obs = all_objects h" using wf by (simp add: is_compatible_observation_def)
  have obj_unique: "\<exists>!ob. ob \<in> all_objects obs \<and> key ob = k"
    using unique_objects[OF ot1_in recoverable] by simp
  then have obj_props: "?obj \<in> all_objects obs \<and> key ?obj = k" by (rule theI')
  have aw_in_obj: "aw \<in> all_aops ?obj"
    using aw_in by (auto simp: awrites_of_def all_awrites_def)
  have obj_wf: "\<forall>obj \<in> all_objects h. wf_object obj" using wf by (cases h; auto)
  have "?obj \<in> all_objects h" using obj_props obs_eq by simp
  then have "wf_object_arc_keys ?obj" using obj_wf unfolding wf_object_def by auto
  then have "key aw = key ?obj" using aw_in_obj unfolding wf_object_arc_keys_def by auto
  then have aw_key: "key aw = k" using obj_props by simp
  have "key ow = key aw" using ow_aw compatible_same_key by fastforce
  then have ow_key: "key ow = k" using aw_key by simp
  have "key (a_ops ?at1 ! i) = k"
    using ci ow_key compatible_same_key by fastforce
  have "op_type ow = Write" using ow_in by (cases ot1; auto simp: all_owrites_def)
  then have "op_type (a_ops ?at1 ! i) = Write"
    using ci compatible_same_type by fastforce
  then obtain v1 a r where aw'_eq: "a_ops ?at1 ! i = AWrite k v1 a v r"
    using \<open>key (a_ops ?at1 ! i) = k\<close> post_v by (cases "a_ops ?at1 ! i") auto
  have aw'_in: "AWrite k v1 a v r \<in> set (a_ops ?at1)" using aw'_eq ia nth_mem by fastforce
  have aw'_inter: "is_intermediate_awrite (a_ops ?at1) k (AWrite k v1 a v r)"
    using inter_a aw'_eq by simp
  show ?thesis
    unfolding has_g1b_def
    using at1_in at2_in at1_comm at2_comm aw'_in aw'_inter read_in_at2 by blast
qed


section \<open>Inferred Dirty Updates\<close>

text \<open>A dirty update is inferred when an aborted transaction is recoverable to a version vi,
and a committed transaction has a write with known pre-version vi on the same key.\<close>

definition has_idirty_update :: "observation \<Rightarrow> bool" where
"has_idirty_update obs \<equiv> (\<exists>t1 t2 k vi ow2.
  t1 \<in> all_otxns obs \<and> t2 \<in> all_otxns obs \<and>
  o_is_committed t1 = Some False \<and>
  o_is_committed t2 = Some True \<and>
  is_recoverable obs k vi t1 \<and>
  ow2 \<in> all_owrites t2 \<and>
  key ow2 = k \<and>
  pre_version ow2 = Some vi)"

text \<open>Soundness: if an observation exhibits an inferred dirty update, every well-formed
interpretation exhibits a dirty update in its history.\<close>

theorem idirty_update_sound:
  assumes ig: "has_idirty_update obs"
  and wf: "wf_interpretation (Interp obs m h)"
  and write_definite: "\<And>ot k v obj ow aw.
    \<lbrakk>ot \<in> all_otxns obs; is_recoverable obs k v ot;
     obj = (THE ob. ob \<in> all_objects obs \<and> key ob = k);
     ow \<in> all_owrites ot; aw \<in> awrites_of obj v;
     is_compatible_op ow aw\<rbrakk> \<Longrightarrow> post_version ow \<noteq> None"
  and unique_objects: "\<And>k v ot. \<lbrakk>ot \<in> all_otxns obs; is_recoverable obs k v ot\<rbrakk>
    \<Longrightarrow> \<exists>!ob. ob \<in> all_objects obs \<and> key ob = k"
  shows "has_dirty_update h"
proof -
  from ig obtain ot1 ot2 k vi ow2 where
    ot1_in: "ot1 \<in> all_otxns obs" and ot2_in: "ot2 \<in> all_otxns obs" and
    ot1_aborted: "o_is_committed ot1 = Some False" and
    ot2_committed: "o_is_committed ot2 = Some True" and
    recoverable: "is_recoverable obs k vi ot1" and
    ow2_in: "ow2 \<in> all_owrites ot2" and
    ow2_key: "key ow2 = k" and
    ow2_pre: "pre_version ow2 = Some vi"
    unfolding has_idirty_update_def by blast
  let ?at1 = "m ot1" and ?at2 = "m ot2"
  have at1_in: "?at1 \<in> all_atxns h" using wf ot1_in wf_interp_m_in_h by blast
  have at2_in: "?at2 \<in> all_atxns h" using wf ot2_in wf_interp_m_in_h by blast
  have compat1: "is_compatible_txn ot1 ?at1" using wf ot1_in wf_interp_compatible by blast
  have compat2: "is_compatible_txn ot2 ?at2" using wf ot2_in wf_interp_compatible by blast
  have at1_aborted: "\<not>(a_is_committed ?at1)"
    using compat1 ot1_aborted compatible_committed_state by fastforce
  have at2_committed: "a_is_committed ?at2"
    using compat2 ot2_committed compatible_committed_state by fastforce

  text \<open>at1 has a write producing vi (same as G1a).\<close>
  have write_in_at1: "\<exists>v1 a r. AWrite k v1 a vi r \<in> all_aops ?at1"
  proof -
    let ?obj = "THE ob. ob \<in> all_objects obs \<and> key ob = k"
    from recoverable obtain aw ow where
      aw_in: "aw \<in> awrites_of ?obj vi" and
      ow_in: "ow \<in> all_owrites ot1" and
      ow_aw_compat: "is_compatible_op ow aw"
      unfolding is_recoverable_def could_have_been_written_by_def by (auto simp: Let_def)
    have ow_in_ops: "ow \<in> set (o_ops ot1)"
      using ow_in by (cases ot1; auto simp: all_owrites_def)
    have "is_compatible_op_list (o_ops ot1) (a_ops ?at1)"
      using compat1 by (cases ot1; cases ?at1; simp add: is_compatible_txn_def)
    then obtain aw' where aw'_in: "aw' \<in> set (a_ops ?at1)"
      and ow_aw'_compat: "is_compatible_op ow aw'"
      using compatible_op_list_member ow_in_ops by blast
    have "post_version ow \<noteq> None"
      using write_definite[OF ot1_in recoverable refl ow_in aw_in ow_aw_compat] by simp
    then obtain pv where pv: "post_version ow = Some pv" by auto
    have "apost_version aw = pv" using ow_aw_compat pv compatible_write_definite_post by blast
    moreover have "apost_version aw' = pv"
      using ow_aw'_compat pv compatible_write_definite_post by blast
    moreover have "apost_version aw = vi"
      using aw_in by (auto simp: awrites_of_def all_awrites_def)
    ultimately have post_v: "apost_version aw' = vi" by simp
    have aw_in_obj: "aw \<in> all_aops ?obj"
      using aw_in by (auto simp: awrites_of_def all_awrites_def)
    have obs_eq: "all_objects obs = all_objects h"
      using wf by (simp add: is_compatible_observation_def)
    have obj_wf: "\<forall>obj \<in> all_objects h. wf_object obj"
      using wf by (cases h; auto)
    have obj_unique: "\<exists>!ob. ob \<in> all_objects obs \<and> key ob = k"
      using unique_objects[OF ot1_in recoverable] by simp
    then have obj_props: "?obj \<in> all_objects obs \<and> key ?obj = k" by (rule theI')
    have "?obj \<in> all_objects h" using obj_props obs_eq by simp
    then have "wf_object_arc_keys ?obj" using obj_wf unfolding wf_object_def by auto
    then have "key aw = key ?obj" using aw_in_obj unfolding wf_object_arc_keys_def by auto
    then have aw_key: "key aw = k" using obj_props by simp
    have keys_eq: "key aw' = key aw"
    proof -
      have "key ow = key aw'" using ow_aw'_compat compatible_same_key by fastforce
      moreover have "key ow = key aw" using ow_aw_compat compatible_same_key by fastforce
      ultimately show ?thesis by simp
    qed
    have aw'_key: "key aw' = k" using keys_eq aw_key by simp
    have "op_type ow = Write" using ow_in by (cases ot1; auto simp: all_owrites_def)
    then have "op_type aw' = Write" using ow_aw'_compat compatible_same_type by fastforce
    then obtain v1 a r where "aw' = AWrite k v1 a vi r"
      using aw'_key post_v by (cases aw') auto
    moreover have "aw' \<in> all_aops ?at1" using aw'_in by (cases ?at1) auto
    ultimately show ?thesis by blast
  qed

  text \<open>at2 has a write with pre-version vi.\<close>
  have write_in_at2: "\<exists>a2 v2 r2. AWrite k vi a2 v2 r2 \<in> all_aops ?at2"
  proof -
    have ow2_in_ops: "ow2 \<in> set (o_ops ot2)"
      using ow2_in by (cases ot2; auto simp: all_owrites_def)
    have "is_compatible_op_list (o_ops ot2) (a_ops ?at2)"
      using compat2 by (cases ot2; cases ?at2; simp add: is_compatible_txn_def)
    then obtain aw2 where aw2_in: "aw2 \<in> set (a_ops ?at2)"
      and ow2_aw2_compat: "is_compatible_op ow2 aw2"
      using compatible_op_list_member ow2_in_ops by blast
    have aw2_pre: "apre_version aw2 = vi"
      using ow2_aw2_compat ow2_pre compatible_write_definite_pre by blast
    have aw2_key: "key aw2 = k"
      using ow2_aw2_compat ow2_key compatible_same_key by fastforce
    have "op_type ow2 = Write"
      using ow2_in by (cases ot2; auto simp: all_owrites_def)
    then have "op_type aw2 = Write"
      using ow2_aw2_compat compatible_same_type by fastforce
    then obtain a2 v2 r2 where "aw2 = AWrite k vi a2 v2 r2"
      using aw2_key aw2_pre by (cases aw2) auto
    moreover have "aw2 \<in> all_aops ?at2" using aw2_in by (cases ?at2) auto
    ultimately show ?thesis by blast
  qed

  from write_in_at1 obtain v1 a1 r1 where w1: "AWrite k v1 a1 vi r1 \<in> all_aops ?at1" by blast
  from write_in_at2 obtain a2 v2 r2 where w2: "AWrite k vi a2 v2 r2 \<in> all_aops ?at2" by blast
  show ?thesis
    unfolding has_dirty_update_def
    using at1_in at2_in at1_aborted at2_committed w1 w2 by blast
qed

end
