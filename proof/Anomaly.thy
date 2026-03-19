theory Anomaly
  imports Main DSG Observation
begin

section \<open>Non-Cyclic Anomalies\<close>

text \<open>We are now ready to encode notions of Adya's anomalies. An aborted read, or g1a, implies some
pair of transactions exist such that one wrote v1 and aborted, and another read v1 and committed.\<close>

definition has_g1a :: "history \<Rightarrow> bool" where
"has_g1a h \<equiv> (\<exists>t1 t2 k v1 a v2 r. (t1 \<in> (all_atxns h)) \<and>
                                  (t2 \<in> (all_atxns h)) \<and>
                                  (\<not>(a_is_committed t1)) \<and>
                                  (a_is_committed t2) \<and>
                                  (AWrite k v1 a v2 r) \<in> (all_aops t1) \<and>
                                  (ARead k v2) \<in> (all_aops t2))"

text \<open>An empty history does not have an aborted read. We use key variables since key is opaque.\<close>

lemma "\<not>(has_g1a (History {(register k)} {} {(KeyVersionOrder k [[0]])}))"
  by (simp add:has_g1a_def)

text "But this history does: we write 1 and fail to commit, then read it! We don't actually
have to constrain the version order for this to happen, either."

lemma "has_g1a (History {(register k)}
                        {(ATxn [(AWrite k [0] 1 [1] [])] False),
                         (ATxn [(ARead k [1])] True)}
                        kvo)"
  using has_g1a_def by fastforce

text \<open>An intermediate read, or G1b, implies a committed transaction t2 reads a version v2 of key k
that was produced by a non-final write of another committed transaction t1. A write is non-final
(intermediate) if there exists a later write to the same key in the same transaction.\<close>

definition is_intermediate_awrite :: "aop list \<Rightarrow> key \<Rightarrow> aop \<Rightarrow> bool" where
"is_intermediate_awrite ops k w \<equiv>
  (\<exists>i j. i < length ops \<and> j < length ops \<and> i < j \<and>
         ops ! i = w \<and> op_type (ops ! j) = Write \<and> key (ops ! j) = k)"

definition has_g1b :: "history \<Rightarrow> bool" where
"has_g1b h \<equiv> (\<exists>t1 t2 k v1 a v2 r. (t1 \<in> (all_atxns h)) \<and>
                                  (t2 \<in> (all_atxns h)) \<and>
                                  (a_is_committed t1) \<and>
                                  (a_is_committed t2) \<and>
                                  (AWrite k v1 a v2 r) \<in> set (a_ops t1) \<and>
                                  is_intermediate_awrite (a_ops t1) k (AWrite k v1 a v2 r) \<and>
                                  (ARead k v2) \<in> (all_aops t2))"

text \<open>A dirty update occurs when a committed transaction T2 contains a write which acts on a
version produced by an uncommitted (aborted) transaction T1. Information from the aborted
transaction leaks into the committed state via writes rather than reads.\<close>

definition has_dirty_update :: "history \<Rightarrow> bool" where
"has_dirty_update h \<equiv> (\<exists>t1 t2 k v1 a1 vi r1 a2 v2 r2.
  (t1 \<in> (all_atxns h)) \<and> (t2 \<in> (all_atxns h)) \<and>
  (\<not>(a_is_committed t1)) \<and> (a_is_committed t2) \<and>
  (AWrite k v1 a1 vi r1) \<in> (all_aops t1) \<and>
  (AWrite k vi a2 v2 r2) \<in> (all_aops t2))"

section \<open>Cyclic Anomalies\<close>

text \<open>In an G0 anomaly, a cycle exists in the DSG composed purely of write dependencies.\<close>

definition has_g0 :: "history \<Rightarrow> bool" where
"has_g0 h \<equiv> (\<exists>path. (cycle (dsg h) path) \<and> ((path_dep_types path) = {WW}))"

text \<open>For example...\<close>

text \<open>We show ww-depends by providing explicit write witnesses and unfolding the definitions.
The key steps: (1) each write is in ext_awrites because it's the last write to its key in the
transaction, (2) they share the same key x, and (3) v1 immediately precedes v2 in the version
order for x.\<close>

lemma ww_depends_ex:
  assumes "(distinct [x,y]) \<and> (distinct [v0,v1,v2])"
  shows "ww_depends (History objs
                         {(ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True),
                          (ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True)}
                         {(KeyVersionOrder x [v0,v1,v2]),
                          (KeyVersionOrder y [v0,v1,v2])})
                      (ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True)
                      (ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True)"
proof -
  have xy: "x \<noteq> y" and dv: "v0 \<noteq> v1" "v0 \<noteq> v2" "v1 \<noteq> v2" using assms by auto
  let ?t1 = "ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True"
  let ?t2 = "ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True"
  let ?h = "History objs {?t1, ?t2}
              {(KeyVersionOrder x [v0,v1,v2]), (KeyVersionOrder y [v0,v1,v2])}"
  let ?w1 = "AWrite x v0 a1 v1 r1"
  let ?w2 = "AWrite x v1 a2 v2 r2"
  have w1_in: "?w1 \<in> ext_awrites ?t1" using xy by (auto simp: ran_def)
  have w2_in: "?w2 \<in> ext_awrites ?t2" using xy by (auto simp: ran_def)
  have next_h: "is_next_in_history ?h x v1 v2"
    unfolding is_next_in_history_def
    apply simp
    apply (rule_tac x="KeyVersionOrder x [v0, v1, v2]" in exI)
    using dv by auto
  show ?thesis
    unfolding ww_depends_def
    apply (rule_tac x="?w1" in exI)
    apply (rule_tac x="?w2" in exI)
    using w1_in w2_in next_h by simp
qed

text \<open>The has_g0 example requires constructing a full cycle in the DSG. This involves
two ww-dependency edges (one per key) forming a cycle between the two transactions.\<close>

text \<open>We also need the reverse direction: t2 ww-depends on t1 via key y.\<close>

lemma ww_depends_ex_rev:
  assumes "(distinct [x,y]) \<and> (distinct [v0,v1,v2])"
  shows "ww_depends (History objs
                         {(ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True),
                          (ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True)}
                         {(KeyVersionOrder x [v0,v1,v2]),
                          (KeyVersionOrder y [v0,v1,v2])})
                      (ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True)
                      (ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True)"
proof -
  have xy: "x \<noteq> y" and dv: "v0 \<noteq> v1" "v0 \<noteq> v2" "v1 \<noteq> v2" using assms by auto
  let ?t1 = "ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True"
  let ?t2 = "ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True"
  let ?h = "History objs {?t1, ?t2}
              {(KeyVersionOrder x [v0,v1,v2]), (KeyVersionOrder y [v0,v1,v2])}"
  have w1_in: "AWrite y v0 a1 v1 r1 \<in> ext_awrites ?t2" using xy by (auto simp: ran_def)
  have w2_in: "AWrite y v1 a2 v2 r2 \<in> ext_awrites ?t1" using xy by (auto simp: ran_def)
  have next_h: "is_next_in_history ?h y v1 v2"
    unfolding is_next_in_history_def
    apply simp
    apply (rule_tac x="KeyVersionOrder y [v0, v1, v2]" in exI)
    using dv by auto
  show ?thesis
    unfolding ww_depends_def
    apply (rule_tac x="AWrite y v0 a1 v1 r1" in exI)
    apply (rule_tac x="AWrite y v1 a2 v2 r2" in exI)
    using w1_in w2_in next_h by simp
qed

text \<open>Now we construct the cycle. The DSG uses tail=adep_tail (third component) and
head=adep_head (first component). For ADep t1 WW t2, tail=t2 and head=t1.
So the cycle path [ADep t2 WW t1, ADep t1 WW t2] starts at tail(e1)=t1,
goes to head(e1)=t2, then tail(e2)=t2 matches, and head(e2)=t1 completes the cycle.\<close>

lemma has_g0_ex:
  assumes "(distinct [x,y]) \<and> (distinct [v0,v1,v2])"
  shows "has_g0 (History objs
                         {(ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True),
                          (ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True)}
                         {(KeyVersionOrder x [v0,v1,v2]),
                          (KeyVersionOrder y [v0,v1,v2])})"
proof -
  have xy: "x \<noteq> y" using assms by auto
  let ?t1 = "ATxn [(AWrite x v0 a1 v1 r1), (AWrite y v1 a2 v2 r2)] True"
  let ?t2 = "ATxn [(AWrite y v0 a1 v1 r1), (AWrite x v1 a2 v2 r2)] True"
  let ?h = "History objs {?t1, ?t2}
              {(KeyVersionOrder x [v0,v1,v2]), (KeyVersionOrder y [v0,v1,v2])}"
  let ?G = "dsg ?h"
  have ww12: "ww_depends ?h ?t1 ?t2" using ww_depends_ex assms by blast
  have ww21: "ww_depends ?h ?t2 ?t1" using ww_depends_ex_rev assms by blast
  let ?e1 = "ADep ?t2 WW ?t1"
  let ?e2 = "ADep ?t1 WW ?t2"
  let ?p = "[?e1, ?e2]"
  have e1_in: "?e1 \<in> arcs ?G" using ww21 by (auto simp: dsg_def)
  have e2_in: "?e2 \<in> arcs ?G" using ww12 by (auto simp: dsg_def)
  have t1_vert: "?t1 \<in> verts ?G" by (simp add: dsg_def)
  have t1_ne_t2: "?t1 \<noteq> ?t2" using xy by auto
  have cas_ok: "cas ?G ?t1 ?p ?t1" by (simp add: dsg_def)
  have path_ok: "path ?G ?t1 ?p ?t1"
    unfolding path_def using t1_vert e1_in e2_in cas_ok by auto
  have dist_ok: "distinct (tl (path_verts ?G ?t1 ?p))"
    using t1_ne_t2 by (simp add: dsg_def)
  have "cycle ?G ?p"
    unfolding cycle_def using path_ok dist_ok by auto
  moreover have "path_dep_types ?p = {WW}" by simp
  ultimately show ?thesis unfolding has_g0_def by blast
qed

text \<open>A G1c anomaly is a cycle comprised of write-write and write-read dependencies. We diverge from
Adya here in classifying G0 and G1c as distinct classes; feels more useful to distinguish them.\<close>

definition has_g1c :: "history \<Rightarrow> bool" where
"has_g1c h \<equiv> (\<exists>path. (cycle (dsg h) path) \<and> ((path_dep_types path) = {WW,WR}))"

text \<open>And a G2 anomaly is a cycle involving read-write dependencies.\<close>

definition has_g2 :: "history \<Rightarrow> bool" where
"has_g2 h \<equiv> (\<exists>path. (cycle (dsg h) path) \<and> (RW \<in> (path_dep_types path)))"



end