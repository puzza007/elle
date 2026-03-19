theory Object
  imports
    Main Op "graphs/Digraph"
begin

section \<open>Version Graphs\<close>

text \<open>A version graph is a directed graph between versions, whose arcs (edges) are writes.\<close>

type_synonym "versionGraph" = "(version, aop) pre_digraph"

section \<open>Paths\<close>

text \<open>A path is a non-empty list of abstract writes such that each write's postversion connects to
the next write's preversion.\<close>

type_synonym "path" = "aop list"

primrec is_path :: "aop list \<Rightarrow> bool" where
"is_path [] = False" |
"is_path (w1 # ws) = (case ws of [] \<Rightarrow> True | (w2 # _) \<Rightarrow>
                      ((post_version w1) = (pre_version w2)) \<and> (is_path ws))"

lemma "is_path [AWrite k [0] 1 [1] [], AWrite k [1] 2 [2] []]"
  apply auto
  done

text \<open>We can also retrieve every version along a path, including the preversion of the first
write, and the postversion of the last write.\<close>

primrec path_versions :: "aop list \<Rightarrow> version list" where
"path_versions [] = []" |
"path_versions (w # ws) = ((apre_version w) # (map apost_version (w # ws)))"

text \<open>We say a path is in a version graph if every write in the path is in the version graph too.\<close>
primrec is_path_in_graph :: "aop list \<Rightarrow> versionGraph \<Rightarrow> bool" where
"is_path_in_graph [] g = True" |
"is_path_in_graph (w # ws) g = ((w \<in> (Digraph.arcs g)) \<and> (is_path_in_graph ws g))"



section \<open>Objects\<close>

text \<open>We define an Object as a key, an initial version, and a digraph over versions, where arcs
are writes."\<close>

datatype object = Object "key" "version" "versionGraph"

text \<open>Some basic accessors for objects\<close>

instantiation object :: keyed
begin
primrec key_object :: "object \<Rightarrow> key" where
"key_object (Object k i g) = k"
instance ..
end

primrec initial_version :: "object \<Rightarrow> version" where
"initial_version (Object k i g) = i"

primrec version_graph :: "object \<Rightarrow> versionGraph" where
"version_graph (Object k i g) = g"

instantiation object :: all_versions
begin
primrec all_versions_object :: "object \<Rightarrow> version set" where
"all_versions (Object k i g) = (Digraph.verts g)"
instance ..
end

instantiation object :: all_aops
begin
primrec all_aops_object :: "object \<Rightarrow> aop set" where
"all_aops_object (Object k i g) = (Digraph.arcs g)"
instance ..
end

section \<open>Traces\<close>

text \<open>A trace is a path in some object's version graph which connects the initial version to some
chosen version.\<close>

definition is_trace_of :: "object \<Rightarrow> path \<Rightarrow> version \<Rightarrow> bool" where
"is_trace_of obj p v \<equiv> ((is_path p) \<and>
                       (is_path_in_graph p (version_graph obj)) \<and>
                       ((initial_version obj) = (apre_version (hd p))) \<and>
                       (v = (apost_version (last p))))"

text \<open>We say an object is fully reachable if every element other than the initial version has a
trace. The initial version is the starting point of all traces and requires no trace itself.\<close>

definition is_fully_reachable :: "object \<Rightarrow> bool" where
"is_fully_reachable obj \<equiv> (\<forall>v. (v \<in> (all_versions obj) \<and> v \<noteq> (initial_version obj))
                               \<longrightarrow> (\<exists>p. (is_trace_of obj p v)))"




text \<open>We can now define a well-formed object: they are fully reachable, and their initial version
is in the version graph. That second part might be redundant.\<close>

definition wf_object_init_in_graph :: "object \<Rightarrow> bool" where
"wf_object_init_in_graph obj \<equiv> ((initial_version obj) \<in> (all_versions obj))"

definition wf_object_arc_keys :: "object \<Rightarrow> bool" where
"wf_object_arc_keys obj \<equiv> (\<forall>w \<in> all_aops obj. key w = key obj)"

definition wf_object :: "object \<Rightarrow> bool" where
"wf_object obj \<equiv> (wf_object_init_in_graph obj) \<and>
                 (is_fully_reachable obj) \<and>
                 (wf_object_arc_keys obj)"


text \<open>We might want to know the set of all operations which could result in some version.\<close>

definition awrites_of :: "object \<Rightarrow> version \<Rightarrow> aop set" where
"awrites_of obj v \<equiv> {w. w \<in> all_awrites obj \<and> v = apost_version w}"



text \<open>Now, we aim to include a new property: traceability\<close>

text \<open>Does this object have exactly one write resulting in a version?\<close>

definition version_has_only_one_write :: "object \<Rightarrow> version \<Rightarrow> bool" where
"version_has_only_one_write obj v \<equiv> (\<exists>!w. w \<in> awrites_of obj v)"

definition every_version_has_only_one_write :: "object \<Rightarrow> bool" where
"every_version_has_only_one_write obj \<equiv> (\<forall>v. (v \<in> (all_versions obj)) \<longrightarrow>
                                              (version_has_only_one_write obj v))"

definition every_version_has_at_most_one_write :: "object \<Rightarrow> bool" where
"every_version_has_at_most_one_write obj \<equiv> (\<forall>v. (v \<in> (all_versions obj)) \<longrightarrow>
                                                ((\<not>(\<exists>w. (apost_version w) = v)) \<or>
                                                (\<exists>!w. (apost_version w) = v)))"

text \<open>We say an object is traceable if it has exactly one trace for every version other than
the initial version. The initial version is the root of the version graph and has no trace
(since traces require a non-empty path from the initial version).\<close>

definition is_traceable :: "object \<Rightarrow> bool" where
"is_traceable obj \<equiv> (\<forall>v. ((v \<in> (all_versions obj) \<and> v \<noteq> (initial_version obj))
                          \<longrightarrow> (\<exists>!p. (is_trace_of obj p v))))"

(* I don't exactly understand the THE quantifier, but hopefully this works in conjunction with
traceable objects? *)
definition trace_of :: "object \<Rightarrow> version \<Rightarrow> path" where
"trace_of obj version \<equiv> (THE path. is_trace_of obj path version)"

text \<open>For traceable objects, we can define a trace_length for any version.\<close>

definition trace_length :: "object \<Rightarrow> version \<Rightarrow> nat" where
"trace_length obj v \<equiv> (length (trace_of obj v))"


subsection \<open>Implementations of objects\<close>


text \<open>Our digraphs need sets of vertices and arcs. We can write infinite sets, but for debugging and
examples, it's nice to think about finite domains. Let's construct the set of singleton lists up to
size s...\<close>
(* This throws a well-sortedness error value "{(v :: version). True}" *)

primrec nats_up_to :: "nat \<Rightarrow> nat list" where
"nats_up_to 0       = []" |
"nats_up_to (Suc n) = (n # (nats_up_to n))"
value "nats_up_to 2"

(* Takes a list and returns every variant of that list but starting with nats up to n. *)
definition tack_on_nats_up_to :: "nat \<Rightarrow> nat list \<Rightarrow> nat list list" where
"tack_on_nats_up_to n xs \<equiv> (map (\<lambda>x. (x # xs)) (nats_up_to n))"
value "tack_on_nats_up_to 3 (1 # [])"

(* Map and concatenate *)
definition mapcat :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
"mapcat f xs \<equiv> (concat (map f xs))"
value "mapcat nats_up_to (1 # 2 # 3 # [])"

(* Fixed lists *)
primrec lists_of_n_nats_up_to_m :: "nat \<Rightarrow> nat \<Rightarrow> nat list list" where
"lists_of_n_nats_up_to_m 0        m = ([] # [])" |
"lists_of_n_nats_up_to_m (Suc n)  m = (mapcat (tack_on_nats_up_to m) (lists_of_n_nats_up_to_m n m))"
value "lists_of_n_nats_up_to_m 2 2"

(* Variable lists *)
definition lists_of_nats_up_to :: "nat \<Rightarrow> nat list list" where
"lists_of_nats_up_to m \<equiv> (mapcat (\<lambda>n. (lists_of_n_nats_up_to_m (Suc n) m))
                                 (nats_up_to m))"

text \<open>Given a set of versions, an initial version, and a write function which takes a current
version and an argument to a resulting version and return value, we can build an object.\<close>

(*
 (AWrite k v1 a v2 r) | v1 a v2 r. (v1 \<in> domain) \<and>
                                   (v2 \<in> domain) \<and> 
                                   (f v1 a) = (v2,r)},
*)

text \<open>We define a finite object constructor for debugging purposes--this version is executable.\<close>
definition smol_object :: "version list \<Rightarrow> writeArg list \<Rightarrow> version \<Rightarrow>
                           (version \<Rightarrow> writeArg \<Rightarrow> (version \<times> writeRet)) \<Rightarrow> key \<Rightarrow> object" where
"smol_object vs args init f k \<equiv> (Object k init
  \<lparr>verts = (set vs),
   arcs  = (set (mapcat (\<lambda>v1. (mapcat (\<lambda>v2. (mapcat (\<lambda>a.
                  (let (v2,r) = (f v1 a) in
                    (if (v2 \<in> (set vs)) then ((AWrite k v1 a v2 r) # []) else [])))
                  args)) vs)) vs)),
   tail  = apost_version,
   head  = apre_version\<rparr>)"

text \<open>And an object whose values are single-element sets up to the number n, such that writes
always overwrite the current value, and return values are always the empty list.\<close>

definition smol_register :: "nat \<Rightarrow> key \<Rightarrow> object" where
"smol_register n k \<equiv> (smol_object (lists_of_n_nats_up_to_m 1 n)
                                  (nats_up_to n)
                                  (0 # [])
                                  (\<lambda>ver arg. ((arg # []), []))
                                  k)"

value "smol_register 2 k"

text \<open>It's easier to prove properties of infinitely defined registers.\<close>

definition register :: "key \<Rightarrow> object" where
"register k \<equiv> (Object k [0] \<lparr>verts = {[v] | v. v \<in> Nats},
                             arcs  = {(AWrite k [v1] a [a] []) | v1 a. v1 \<in> Nats \<and> a \<in> Nats},
                             tail = apost_version,
                             head = apre_version\<rparr>)"

text \<open>We show that all finite registers can only reach values up to [n].\<close>

lemma "(all_versions (smol_register n k)) = (set (map (\<lambda>x.[x]) (nats_up_to n)))"
  apply (simp add:smol_register_def mapcat_def tack_on_nats_up_to_def
        nats_up_to_def smol_object_def)
  done

text \<open>And that finite nonempty registers are well-formed.\<close>

(* Not working yet
lemma "(0 < n) \<longrightarrow> wf_object (smol_register n k)"
  apply (simp add:wf_object_def wf_object_init_in_graph_def smol_register_def initial_version_def
         smol_object_def mapcat_def tack_on_nats_up_to_def nats_up_to_def)
  apply (induct_tac n)
   apply simp
  apply auto
  done

text \<open>The single-element register is traceable\<close>

lemma smol_singleton_register_traceable: "is_traceable (smol_register n k)"
  apply (simp add:is_traceable_def all_versions_def smol_register_def smol_object_def mapcat_def
tack_on_nats_up_to_def is_trace_of_def nats_up_to_def is_path_def is_path_in_graph_def
apre_version_def apost_version_def)
  (* huh not sure *)
  oops
*)

text \<open>The set of versions of an infinite register is all single-element lists.\<close>

lemma register_versions [simp]: "(all_versions (register k)) = {[x] | x. x \<in> Nats}"
  apply (simp add:register_def)
  done


lemma helper1: "(initial_version (register k)) = [0]"
  by (simp add: register_def)

lemma helper2: "AWrite k [0] (Suc 0) [Suc 0] [] \<in> arcs (version_graph (register k))"
  apply (simp add:register_def)
  by (metis Nats_1 One_nat_def)

lemma zero_in_N: "0 \<in> Nats"
  by auto

lemma n_in_N_implies_suc_in_N: "(n \<in> Nats) \<longrightarrow> (Suc n \<in> Nats)"
  by (metis (full_types) Nats_1 Nats_add One_nat_def add.right_neutral add_Suc_right)

(* REALLY? *)
lemma n_in_N [simp]: "(n::nat) \<in> Nats"
proof -
  obtain nn :: "(nat \<Rightarrow> bool) \<Rightarrow> nat" where
    f1: "\<forall>p n. (\<not> p 0 \<or> p (nn p) \<and> \<not> p (Suc (nn p))) \<or> p n"
    using nat_induct by moura
  have "(0::nat) \<in> \<nat> \<and> (nn (\<lambda>n. n \<in> \<nat>) \<notin> \<nat> \<or> Suc (nn (\<lambda>n. n \<in> \<nat>)) \<in> \<nat>)"
    using n_in_N_implies_suc_in_N by force
  then show ?thesis
    using f1 by (metis (no_types))
qed

(* I am... shocked this is this complicated *)
lemma succ_n_in_N [simp]: "(Suc n) \<in> Nats"
  by (simp add:n_in_N)

lemma helper3: "AWrite k [Suc 0] n [n] [] \<in> arcs (version_graph (register k))"
  by (simp add:register_def)

text \<open>There is a single-write trace to any version.\<close>

lemma register_one_trace: "is_trace_of (register k) [AWrite k [0] n [n] []] [n]"
  apply (simp add:is_trace_of_def register_def)
  done

text \<open>There is a second trace to any version going 0\<rightarrow>1\<rightarrow>v\<close>

lemma register_two_trace: "is_trace_of (register k) [(AWrite k [0] 1 [1] []),
                                                     (AWrite k [1] n [n] [])] [n]"
  unfolding is_trace_of_def
  apply auto
    apply (simp add:helper2)
   apply (simp add:helper3)
  by (simp add: helper1)

lemma register_has_a_trace: "\<exists>p. is_trace_of (register k) p [n]"
  using register_two_trace by blast

(* not working yet
lemma register_has_two_traces: "let r = (register k) in \<exists>p1 p2. (is_trace_of r p1 [n]) \<and>
                                                                (is_trace_of r p2 [n]) \<and>
                                                                (p \<noteq> q)"
proof-
  { fix x assume "x = 2" }
  using register_one_trace
  using register_two_trace

lemma register_not_traceable: "~(is_traceable (register k))"
  oops
*)

subsection \<open>Next, we define a construct for a list-append object. The initial value is the empty
list, and writes append an entry to the end of the list.\<close>

definition list_append :: "key \<Rightarrow> object" where
"list_append k \<equiv> (Object k [] \<lparr>verts = {l::(nat list). True},
                               arcs  = {(AWrite k v a (v @ [a]) []) | v a. a \<in> Nats },
                               tail  = apost_version,
                               head  = apre_version\<rparr>)"

text \<open>We wish to show that list append is traceable. We can show that a singleton list has a trace
if we feed that trace to the checker...\<close>

lemma list_append_singleton_list_has_trace_definite:
  "is_trace_of (list_append k) [(AWrite k [] x1 [x1] [])] [x1]"
  apply (simp add:is_trace_of_def list_append_def)
  done

text \<open>We can derive the existential from the definite witness via blast.\<close>

lemma list_append_singleton_list_has_trace: "\<exists>p. is_trace_of (list_append k) p [x1]"
  using list_append_singleton_list_has_trace_definite by blast

text \<open>To prove list append is traceable, we need to show that every non-empty list has a unique
trace. We first define a function that constructs the trace for a given version, then show
it is the unique valid trace.

The trace of [v1, v2, ..., vn] from [] is the path:
  [AWrite k [] v1 [v1] [], AWrite k [v1] v2 [v1,v2] [], ..., AWrite k [v1,...,v_{n-1}] vn [v1,...,vn] []]

Existence follows by induction on the list. Uniqueness follows because each version xs@[x]
has exactly one incoming arc (AWrite k xs x (xs@[x]) []), so the predecessor is determined,
and by induction the trace to the predecessor is unique.\<close>

fun list_append_trace :: "key \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> path" where
"list_append_trace k prefix [] = []" |
"list_append_trace k prefix (x # rest) =
  (AWrite k prefix x (prefix @ [x]) []) # (list_append_trace k (prefix @ [x]) rest)"

text \<open>Some helper lemmas about list_append arcs.\<close>

lemma list_append_arc_form:
  "w \<in> arcs (version_graph (list_append k)) \<Longrightarrow>
   \<exists>v a. w = AWrite k v a (v @ [a]) [] \<and> a \<in> Nats"
  by (auto simp: list_append_def)

lemma list_append_arc_unique_preversion:
  assumes "AWrite k pre1 arg1 post ret1 \<in> arcs (version_graph (list_append k))"
  and     "AWrite k pre2 arg2 post ret2 \<in> arcs (version_graph (list_append k))"
  shows   "pre1 = pre2 \<and> arg1 = arg2 \<and> ret1 = ret2"
proof -
  from assms(1) obtain v1 a1 where
    h1: "AWrite k pre1 arg1 post ret1 = AWrite k v1 a1 (v1 @ [a1]) []"
    by (auto simp: list_append_def)
  from assms(2) obtain v2 a2 where
    h2: "AWrite k pre2 arg2 post ret2 = AWrite k v2 a2 (v2 @ [a2]) []"
    by (auto simp: list_append_def)
  from h1 have "post = v1 @ [a1]" and "pre1 = v1" and "arg1 = a1" and "ret1 = []" by auto
  from h2 have "post = v2 @ [a2]" and "pre2 = v2" and "arg2 = a2" and "ret2 = []" by auto
  then show ?thesis
    using \<open>post = v1 @ [a1]\<close> \<open>pre1 = v1\<close> \<open>arg1 = a1\<close> \<open>ret1 = []\<close>
    by (metis append_butlast_last_id butlast_snoc last_snoc)
qed

lemma list_append_no_arc_to_nil:
  assumes "w \<in> arcs (version_graph (list_append k))"
  shows "apost_version w \<noteq> []"
proof -
  from assms obtain v a where "w = AWrite k v a (v @ [a]) []" by (auto simp: list_append_def)
  then show ?thesis by auto
qed

text \<open>Properties of the trace construction.\<close>

lemma list_append_trace_nonempty:
  "v \<noteq> [] \<Longrightarrow> list_append_trace k prefix v \<noteq> []"
  by (cases v) auto

lemma list_append_trace_hd_pre:
  "v \<noteq> [] \<Longrightarrow> apre_version (hd (list_append_trace k prefix v)) = prefix"
  by (cases v) auto

lemma list_append_trace_last_post:
  "v \<noteq> [] \<Longrightarrow> apost_version (last (list_append_trace k prefix v)) = prefix @ v"
proof (induct v arbitrary: prefix)
  case Nil
  then show ?case by simp
next
  case (Cons x rest)
  show ?case
  proof (cases rest)
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    then show ?thesis using Cons.hyps[of "prefix @ [x]"] by simp
  qed
qed

text \<open>The snoc decomposition: building a trace to xs@[x] is the same as building
a trace to xs and then appending the final arc.\<close>

lemma list_append_trace_snoc:
  "list_append_trace k prefix (xs @ [x]) =
   list_append_trace k prefix xs @ [AWrite k (prefix @ xs) x (prefix @ xs @ [x]) []]"
proof (induct xs arbitrary: prefix)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case by simp
qed

text \<open>The trace construction produces valid paths. We case-split on the tail to handle the
is_path case expression which distinguishes singleton vs longer lists.\<close>

lemma list_append_trace_is_path:
  "v \<noteq> [] \<Longrightarrow> is_path (list_append_trace k prefix v)"
proof (induct v arbitrary: prefix)
  case Nil
  then show ?case by simp
next
  case (Cons x rest)
  show ?case
  proof (cases rest)
    case Nil
    then show ?thesis by simp
  next
    case (Cons y ys)
    have "is_path (list_append_trace k (prefix @ [x]) rest)"
      using Cons.hyps[of "prefix @ [x]"] local.Cons by simp
    then show ?thesis using local.Cons by simp
  qed
qed

text \<open>Every arc in a trace is in the version graph. The key fact is that every nat is in Nats
(lemma n_in_N), so AWrite k prefix x (prefix@[x]) [] is always a valid arc.\<close>

lemma list_append_trace_in_graph:
  "is_path_in_graph (list_append_trace k prefix v) (version_graph (list_append k))"
proof (induct v arbitrary: prefix)
  case Nil
  then show ?case by simp
next
  case (Cons x rest)
  then show ?case by (auto simp: list_append_def)
qed

text \<open>Combining the above: the canonical trace is a valid trace.\<close>

lemma list_append_trace_correct:
  "v \<noteq> [] \<Longrightarrow> is_trace_of (list_append k) (list_append_trace k [] v) v"
  unfolding is_trace_of_def
  using list_append_trace_is_path list_append_trace_in_graph
        list_append_trace_hd_pre list_append_trace_last_post
  by (simp add: list_append_def)


text \<open>To prove uniqueness, we decompose paths from the end. We use append-based helpers
which are easier to prove than butlast-based ones.\<close>

lemma is_path_in_graph_last:
  "is_path_in_graph p g \<Longrightarrow> p \<noteq> [] \<Longrightarrow> last p \<in> arcs g"
  by (induct p) (auto split: list.splits)

lemma is_path_in_graph_butlast:
  "is_path_in_graph p g \<Longrightarrow> is_path_in_graph (butlast p) g"
  by (induct p) (auto split: list.splits)

lemma is_path_append_single:
  "is_path (p @ [w]) \<Longrightarrow> p \<noteq> [] \<Longrightarrow> is_path p"
proof (induct p)
  case Nil then show ?case by simp
next
  case (Cons a rest) then show ?case by (cases rest) auto
qed

lemma is_path_last_append:
  "is_path (p @ [w]) \<Longrightarrow> p \<noteq> [] \<Longrightarrow>
   post_version (last p) = pre_version w"
proof (induct p)
  case Nil then show ?case by simp
next
  case (Cons a rest) then show ?case by (cases rest) auto
qed

lemma is_path_butlast:
  assumes "is_path p" "length p > 1"
  shows "is_path (butlast p)"
proof -
  from assms(2) have "p \<noteq> []" by auto
  then have peq: "p = butlast p @ [last p]" by simp
  from assms(2) have "butlast p \<noteq> []" by (cases p) auto
  then show ?thesis using assms(1) is_path_append_single peq by metis
qed

lemma is_path_last_connects:
  assumes "is_path p" "length p > 1"
  shows "post_version (last (butlast p)) = pre_version (last p)"
proof -
  from assms(2) have "p \<noteq> []" by auto
  then have peq: "p = butlast p @ [last p]" by simp
  from assms(2) have "butlast p \<noteq> []" by (cases p) auto
  then show ?thesis using assms(1) is_path_last_append peq by metis
qed

text \<open>If we have a trace to v and strip the last arc, we get a trace to the preversion
of that last arc (when the path has more than one element).\<close>

lemma trace_butlast:
  assumes "is_trace_of obj p v" and "length p > 1"
  shows "is_trace_of obj (butlast p) (apre_version (last p))"
proof -
  from assms(1) have pf: "is_path p" "is_path_in_graph p (version_graph obj)"
    "initial_version obj = apre_version (hd p)" "v = apost_version (last p)"
    unfolding is_trace_of_def by auto
  have bp_path: "is_path (butlast p)" using pf(1) assms(2) is_path_butlast by blast
  have bp_in_graph: "is_path_in_graph (butlast p) (version_graph obj)"
    using pf(2) is_path_in_graph_butlast by blast
  have bp_nonempty: "butlast p \<noteq> []" using assms(2) by (cases p) auto
  have bp_hd: "hd (butlast p) = hd p" using assms(2) by (cases p) auto
  have bp_last: "apost_version (last (butlast p)) = apre_version (last p)"
  proof -
    have "post_version (last (butlast p)) = pre_version (last p)"
      using pf(1) assms(2) is_path_last_connects by blast
    then show ?thesis by (cases "last (butlast p)"; cases "last p") auto
  qed
  show ?thesis
    unfolding is_trace_of_def
    using bp_path bp_in_graph bp_hd bp_last bp_nonempty pf(3) by auto
qed

text \<open>Taking a prefix of a trace yields a trace to the intermediate version.\<close>

lemma is_path_prefix:
  "is_path (xs @ ys) \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> is_path xs"
proof (induct ys rule: rev_induct)
  case Nil then show ?case by simp
next
  case (snoc y ys)
  show ?case
  proof (cases "xs @ ys")
    case Nil then show ?thesis using snoc.prems(2) by simp
  next
    case (Cons a rest)
    then have "xs @ ys \<noteq> []" by simp
    have "is_path ((xs @ ys) @ [y])" using snoc.prems(1) by simp
    then have "is_path (xs @ ys)" using is_path_append_single \<open>xs @ ys \<noteq> []\<close> by blast
    then show ?thesis using snoc.hyps snoc.prems(2) by simp
  qed
qed

lemma is_path_take:
  "is_path p \<Longrightarrow> n > 0 \<Longrightarrow> n \<le> length p \<Longrightarrow> is_path (take n p)"
proof -
  assume "is_path p" "n > 0" "n \<le> length p"
  then have "p = take n p @ drop n p" by simp
  moreover have "take n p \<noteq> []" using \<open>n > 0\<close> \<open>n \<le> length p\<close> by auto
  ultimately show ?thesis using \<open>is_path p\<close> is_path_prefix by metis
qed

lemma is_path_in_graph_take:
  "is_path_in_graph p g \<Longrightarrow> is_path_in_graph (take n p) g"
proof (induct p arbitrary: n)
  case Nil then show ?case by simp
next
  case (Cons w rest) then show ?case by (cases n) auto
qed

lemma trace_take:
  assumes "is_trace_of obj p v" and "n > 0" and "n \<le> length p"
  shows "is_trace_of obj (take n p) (apost_version (p ! (n - 1)))"
proof -
  from assms(1) have pf: "is_path p" "is_path_in_graph p (version_graph obj)"
    "initial_version obj = apre_version (hd p)" "v = apost_version (last p)"
    unfolding is_trace_of_def by auto
  have tk_path: "is_path (take n p)" using is_path_take[OF pf(1) assms(2,3)] .
  have tk_in_graph: "is_path_in_graph (take n p) (version_graph obj)"
    using is_path_in_graph_take[OF pf(2)] .
  have tk_ne: "take n p \<noteq> []" using assms(2,3) by auto
  have tk_hd: "hd (take n p) = hd p" using assms(2,3) by (cases p) auto
  have "length (take n p) = n" using assms(3) by simp
  then have tk_last: "last (take n p) = p ! (n - 1)"
    using tk_ne nth_take[of "n - 1" n p] assms(2)
    by (simp add: last_conv_nth)
  show ?thesis unfolding is_trace_of_def
    using tk_path tk_in_graph tk_ne tk_hd tk_last pf(3) by auto
qed

text \<open>For traceable objects, if a version v appears as a post-version in the trace to w,
then trace_of obj v is a prefix of trace_of obj w.\<close>

lemma traceable_trace_prefix:
  assumes "is_traceable obj"
  and "is_trace_of obj p w" and "p = trace_of obj w"
  and "i < length p" and "v = apost_version (p ! i)"
  and "v \<in> all_versions obj" and "v \<noteq> initial_version obj"
  shows "\<exists>zs. trace_of obj w = trace_of obj v @ zs"
proof -
  have tk_trace: "is_trace_of obj (take (Suc i) p) v"
    using trace_take[OF assms(2), of "Suc i"] assms(4,5) by simp
  have "take (Suc i) p = trace_of obj v"
  proof -
    from assms(1,6,7) have "\<exists>!q. is_trace_of obj q v" unfolding is_traceable_def by auto
    then show ?thesis using tk_trace theI'[of "\<lambda>q. is_trace_of obj q v"]
      unfolding trace_of_def by (metis the1_equality)
  qed
  then have "trace_of obj v = take (Suc i) p" by simp
  moreover have "take (Suc i) p @ drop (Suc i) p = p" by simp
  ultimately show ?thesis using assms(3) by metis
qed

text \<open>The trace construction is the unique valid trace. We proceed by reverse induction on v:
each version xs@[x] has exactly one incoming arc in the version graph, so the last element of
any trace is determined, and the remaining prefix is a trace to xs which is unique by the IH.\<close>

lemma list_append_trace_unique:
  "is_trace_of (list_append k) p v \<Longrightarrow> v \<noteq> [] \<Longrightarrow> p = list_append_trace k [] v"
proof (induct v arbitrary: p rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  text \<open>v = xs @ [x]. The last arc of p must have postversion xs@[x].\<close>
  from snoc.prems(1) have p_trace: "is_trace_of (list_append k) p (xs @ [x])" by simp
  from p_trace have pf: "is_path p" "is_path_in_graph p (version_graph (list_append k))"
    "initial_version (list_append k) = apre_version (hd p)"
    "xs @ [x] = apost_version (last p)"
    unfolding is_trace_of_def by auto
  from pf(1) have p_nonempty: "p \<noteq> []" using is_path.simps(1) by auto
  note p_path = pf(1) and p_in_graph = pf(2) and p_init = pf(3) and p_last = pf(4)
  text \<open>The last element is an arc with postversion xs@[x].\<close>
  have last_in_graph: "last p \<in> arcs (version_graph (list_append k))"
    using p_in_graph p_nonempty is_path_in_graph_last by blast
  then obtain pre arg where last_form: "last p = AWrite k pre arg (pre @ [arg]) []"
    using list_append_arc_form by (metis aop.exhaust aop.inject)
  have "pre @ [arg] = xs @ [x]" using last_form p_last by simp
  then have pre_is_xs: "pre = xs" and arg_is_x: "arg = x"
    by (metis append_butlast_last_id butlast_snoc last_snoc)+
  have last_is: "last p = AWrite k xs x (xs @ [x]) []"
    using last_form pre_is_xs arg_is_x by simp
  show ?case
  proof (cases "length p = 1")
    case True
    text \<open>p is a singleton. The arc starts from [] (initial version) and goes to xs@[x].
    Since the preversion of this arc is xs and it must equal the initial version [],
    we have xs = [] and v = [x].\<close>
    then obtain w where p_is: "p = [w]" by (metis One_nat_def length_0_conv length_Suc_conv)
    have "w = AWrite k xs x (xs @ [x]) []" using p_is last_is by simp
    moreover have "apre_version w = xs" using calculation by simp
    moreover have "[] = xs" using p_init p_is calculation by (simp add: list_append_def)
    ultimately show ?thesis using p_is by simp
  next
    case False
    text \<open>p has more than one element. Strip the last arc to get a trace to xs.\<close>
    then have len_gt_1: "length p > 1" using p_nonempty
      by (metis One_nat_def Suc_lessI length_greater_0_conv less_one nat_neq_iff)
    have "apre_version (last p) = xs" using last_is by simp
    have butlast_trace: "is_trace_of (list_append k) (butlast p) xs"
      using trace_butlast[OF p_trace len_gt_1] \<open>apre_version (last p) = xs\<close> by simp
    show ?thesis
    proof (cases "xs = []")
      case True
      text \<open>xs = [], so v = [x]. butlast p is a trace to [], but no arc in list_append
      has postversion []. So butlast p must be empty, meaning p was a singleton after all.\<close>
      from butlast_trace have "[] = apost_version (last (butlast p))"
        using True unfolding is_trace_of_def by simp
      moreover have "last (butlast p) \<in> arcs (version_graph (list_append k))"
        using butlast_trace is_path_in_graph_last unfolding is_trace_of_def
        by (metis is_path.simps(1) len_gt_1 length_butlast less_imp_diff_less
                  list.size(3) not_less_zero zero_less_one)
      ultimately have False using list_append_no_arc_to_nil by metis
      then show ?thesis by simp
    next
      case xs_ne: False
      text \<open>xs \<noteq> []. By the IH, butlast p = list_append_trace k [] xs.\<close>
      have bteq: "butlast p = list_append_trace k [] xs"
        using snoc.hyps[OF butlast_trace xs_ne] by simp
      have "p = butlast p @ [last p]"
        using p_nonempty by (metis append_butlast_last_id)
      then have "p = list_append_trace k [] xs @ [AWrite k xs x (xs @ [x]) []]"
        using bteq last_is by simp
      then show ?thesis using list_append_trace_snoc by simp
    qed
  qed
qed

text \<open>Finally, list append is traceable: every non-initial version has a unique trace.\<close>

lemma list_append_traceable: "is_traceable (list_append k)"
  unfolding is_traceable_def
proof (intro allI impI)
  fix v :: "nat list"
  assume "v \<in> all_versions (list_append k) \<and> v \<noteq> initial_version (list_append k)"
  then have "v \<noteq> []" by (simp add: list_append_def)
  show "\<exists>!p. is_trace_of (list_append k) p v"
  proof (rule ex1I)
    show "is_trace_of (list_append k) (list_append_trace k [] v) v"
      using list_append_trace_correct \<open>v \<noteq> []\<close> by simp
  next
    fix p
    assume "is_trace_of (list_append k) p v"
    then show "p = list_append_trace k [] v"
      using list_append_trace_unique \<open>v \<noteq> []\<close> by simp
  qed
qed

end