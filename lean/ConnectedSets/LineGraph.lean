/-
ConnectedSets/LineGraph.lean

Lemma 7.2 of the paper: the number `F G` of all connected subgraphs `(V', E')` of `G`.
* `F_eq` : `F G = |V| + c (lineGraph G)`             (Lemma 7.2(a));
* `c_le_F` : `c G ≤ F G`                              (Lemma 7.2(b), inequality);
* `c_eq_F_iff` : `c G = F G` if and only if `G` is a forest (Lemma 7.2(b), equality);
* `F_lt_of_adj` : adding an edge strictly increases `F`  (Lemma 7.2(c)).

A pair `(S, E)` is a connected subgraph of `G` if `E` is a set of edges of `G` with both ends in
`S`, and the graph with vertex set `S` and edge set `E` is connected. Connectedness is expressed
by `Sep (fromEdgeSet E) S`, which is equivalent to Mathlib's connectedness of
`(fromEdgeSet E).induce S` (`isConnSub_iff`).
-/
import ConnectedSets.Small
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Acyclic

open Finset SimpleGraph

namespace ConnectedSets

variable {V : Type*} [DecidableEq V]

/-- `(S, E)` is a connected subgraph of `G`. -/
def IsConnSub (G : SimpleGraph V) (S : Finset V) (E : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ E, e ∈ G.edgeSet) ∧ (∀ e ∈ E, ∀ v ∈ e, v ∈ S) ∧ Sep (fromEdgeSet (E : Set (Sym2 V))) S

theorem isConnSub_iff (G : SimpleGraph V) (S : Finset V) (E : Finset (Sym2 V)) :
    IsConnSub G S E ↔ (∀ e ∈ E, e ∈ G.edgeSet) ∧ (∀ e ∈ E, ∀ v ∈ e, v ∈ S) ∧
      ((fromEdgeSet (E : Set (Sym2 V))).induce (S : Set V)).Connected := by
  rw [IsConnSub, ← IsConnSet, isConnSet_iff_sep]

open Classical in
/-- The number of connected subgraphs of `G` (the subgraph index of Pandey and Patra). -/
noncomputable def F [Fintype V] (G : SimpleGraph V) : ℕ :=
  #{p : Finset V × Finset (Sym2 V) | IsConnSub G p.1 p.2}

omit [DecidableEq V] in
theorem exists_mem_sym2 (e : Sym2 V) : ∃ x, x ∈ e := by
  induction e using Sym2.ind with
  | h x y => exact ⟨x, Sym2.mem_mk_left x y⟩

/-- The line graph on all of `Sym2 V`: distinct pairs sharing an element. -/
def lineSym (V : Type*) : SimpleGraph (Sym2 V) where
  Adj e f := e ≠ f ∧ ∃ v, v ∈ e ∧ v ∈ f
  symm := ⟨fun _ _ ⟨h1, v, h2, h3⟩ => ⟨Ne.symm h1, v, h3, h2⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

/-- The vertices of a set of edges. -/
def verts [Fintype V] (E : Finset (Sym2 V)) : Finset V := Finset.univ.filter (fun v => ∃ e ∈ E, v ∈ e)

theorem mem_verts [Fintype V] {E : Finset (Sym2 V)} {v : V} : v ∈ verts E ↔ ∃ e ∈ E, v ∈ e := by
  simp [verts]

/-- For a nonempty set of pairs, connectedness of `(verts E, E)` is connectedness of
`E` in the line graph. -/
theorem sep_verts_iff [Fintype V] {E : Finset (Sym2 V)} (hne : E.Nonempty) : Sep (fromEdgeSet (E : Set (Sym2 V))) (verts E) ↔ Sep (lineSym V) E := by
  constructor
  · intro hS
    refine ⟨hne, fun B hBE hBne hBE' => ?_⟩
    by_cases hA : verts B = verts E
    · obtain ⟨f, hfE, hfB⟩ : ∃ f ∈ E, f ∉ B := by
        by_contra hcon; push Not at hcon
        exact hBE' (Finset.Subset.antisymm hBE hcon)
      obtain ⟨x, hx⟩ := exists_mem_sym2 f
      have : x ∈ verts B := by rw [hA]; exact mem_verts.2 ⟨f, hfE, hx⟩
      obtain ⟨e, heB, hxe⟩ := mem_verts.1 this
      exact ⟨e, heB, f, hfE, hfB, fun h => hfB (h ▸ heB), x, hxe, hx⟩
    · have hsub : verts B ⊆ verts E := by
        intro v hv
        obtain ⟨e, he, hve⟩ := mem_verts.1 hv
        exact mem_verts.2 ⟨e, hBE he, hve⟩
      obtain ⟨e0, he0⟩ := hBne
      obtain ⟨x0, hx0⟩ := exists_mem_sym2 e0
      obtain ⟨a, ha, b, hb, hbA, hab⟩ :=
        hS.2 (verts B) hsub ⟨x0, mem_verts.2 ⟨e0, he0, hx0⟩⟩ hA
      rw [fromEdgeSet_adj] at hab
      obtain ⟨e, heB, hae⟩ := mem_verts.1 ha
      have hfB : s(a, b) ∉ B := fun h => hbA (mem_verts.2 ⟨_, h, Sym2.mem_mk_right a b⟩)
      exact ⟨e, heB, s(a, b), hab.1, hfB, fun h => hfB (h ▸ heB), a, hae, Sym2.mem_mk_left a b⟩
  · intro hL
    obtain ⟨e0, he0⟩ := hne
    obtain ⟨x0, hx0⟩ := exists_mem_sym2 e0
    refine ⟨⟨x0, mem_verts.2 ⟨e0, he0, hx0⟩⟩, fun A hA hAne hAS => ?_⟩
    by_contra hcon
    push Not at hcon
    -- no edge leaves `A`, so edges meeting `A` lie inside `A`
    have hclos : ∀ e ∈ E, ∀ x ∈ e, x ∈ A → ∀ y ∈ e, y ∈ A := by
      intro e he x hx hxA y hy
      by_cases hxy : x = y
      · rw [← hxy]; exact hxA
      by_contra hyA
      have he' : e = s(x, y) := (Sym2.mem_and_mem_iff hxy).1 ⟨hx, hy⟩
      have := hcon x hxA y (mem_verts.2 ⟨e, he, hy⟩) hyA
      rw [fromEdgeSet_adj] at this
      exact this ⟨he' ▸ he, hxy⟩
    set B := E.filter (fun e => ∃ v ∈ e, v ∈ A) with hB
    obtain ⟨a, ha⟩ := hAne
    obtain ⟨ea, hea, hae⟩ := mem_verts.1 (hA ha)
    have hBne : B.Nonempty := ⟨ea, by simp only [hB, Finset.mem_filter]; exact ⟨hea, a, hae, ha⟩⟩
    have hBE' : B ≠ E := by
      obtain ⟨v, hvE, hvA⟩ : ∃ v ∈ verts E, v ∉ A := by
        by_contra hc; push Not at hc
        exact hAS (Finset.Subset.antisymm hA hc)
      obtain ⟨f, hfE, hvf⟩ := mem_verts.1 hvE
      intro hBE
      have hfB : f ∈ B := hBE ▸ hfE
      simp only [hB, Finset.mem_filter] at hfB
      obtain ⟨-, w, hwf, hwA⟩ := hfB
      exact hvA (hclos f hfE w hwf hwA v hvf)
    obtain ⟨e, heB, f, hfE, hfB, -, w, hwe, hwf⟩ :=
      hL.2 B (Finset.filter_subset _ _) hBne hBE'
    simp only [hB, Finset.mem_filter] at heB
    obtain ⟨heE, x, hxe, hxA⟩ := heB
    have hwA : w ∈ A := hclos e heE x hxe hxA w hwe
    exact hfB (by simp only [hB, Finset.mem_filter]; exact ⟨hfE, w, hwf, hwA⟩)

/-- A connected subgraph with at least one edge has vertex set `verts E`. -/
theorem eq_verts_of_isConnSub [Fintype V] {G : SimpleGraph V} {S : Finset V} {E : Finset (Sym2 V)}
    (h : IsConnSub G S E) (hne : E.Nonempty) : S = verts E := by
  obtain ⟨-, hends, hsep⟩ := h
  apply Finset.Subset.antisymm
  · intro v hv
    by_contra hvE
    obtain ⟨e0, he0⟩ := hne
    obtain ⟨x0, hx0⟩ := exists_mem_sym2 e0
    have hne' : ({v} : Finset V) ≠ S := by
      intro h
      have : x0 ∈ ({v} : Finset V) := h ▸ hends e0 he0 x0 hx0
      rw [Finset.mem_singleton] at this
      exact hvE (mem_verts.2 ⟨e0, he0, this ▸ hx0⟩)
    obtain ⟨a, ha, b, -, -, hab⟩ :=
      hsep.2 {v} (Finset.singleton_subset_iff.2 hv) (Finset.singleton_nonempty v) hne'
    rw [Finset.mem_singleton] at ha
    subst ha
    rw [fromEdgeSet_adj] at hab
    exact hvE (mem_verts.2 ⟨_, hab.1, Sym2.mem_mk_left _ _⟩)
  · intro v hv
    obtain ⟨e, he, hve⟩ := mem_verts.1 hv
    exact hends e he v hve

/-- **Lemma 7.2(a)**: `F G = |V| + c (lineGraph G)`. -/
theorem F_eq [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    F G = Fintype.card V + c G.lineGraph := by
  classical
  unfold F
  rw [← Finset.card_filter_add_card_filter_not
    (s := ({p : Finset V × Finset (Sym2 V) | IsConnSub G p.1 p.2} : Finset _)) (fun p => p.2 = ∅)]
  congr 1
  · -- connected subgraphs without edges: the single vertices
    have : ({p : Finset V × Finset (Sym2 V) | IsConnSub G p.1 p.2} : Finset _).filter
        (fun p => p.2 = ∅) = (Finset.univ : Finset V).image (fun v => (({v} : Finset V),
          (∅ : Finset (Sym2 V)))) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
      constructor
      · rintro ⟨⟨-, -, hsep⟩, h2⟩
        rw [h2, Finset.coe_empty, fromEdgeSet_empty] at hsep
        obtain ⟨v, hv⟩ := (sep_bot_iff _).1 hsep
        exact ⟨v, Prod.ext hv.symm h2.symm⟩
      · rintro ⟨v, rfl⟩
        refine ⟨⟨by simp, by simp, ?_⟩, rfl⟩
        exact sep_singleton _ v
    rw [this, Finset.card_image_of_injective _ (fun v w h => by
      simpa using congrArg Prod.fst h), Finset.card_univ]
  · -- connected subgraphs with edges: the connected sets of the line graph
    rw [c_eq_card_sep]
    let emb : G.edgeSet ↪ Sym2 V := Function.Embedding.subtype _
    have hf : ∀ a b : G.edgeSet, (lineSym V).Adj (emb a) (emb b) ↔ G.lineGraph.Adj a b := by
      intro a b
      rw [lineGraph_adj_iff_exists]
      simp only [lineSym, emb, Function.Embedding.coe_subtype, ne_eq, Subtype.coe_injective.eq_iff]
    symm
    apply Finset.card_nbij' (fun X => (verts (X.map emb), X.map emb))
      (fun p => p.2.subtype (· ∈ G.edgeSet))
    · intro X hX
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hX ⊢
      have hL : Sep (lineSym V) (X.map emb) := (sep_map_emb emb hf X).2 hX
      have hne : (X.map emb).Nonempty := by simpa using hX.1
      refine ⟨⟨?_, ?_, (sep_verts_iff hne).2 hL⟩, ?_⟩
      · intro e he
        simp only [Finset.mem_map, emb, Function.Embedding.coe_subtype] at he
        obtain ⟨x, -, rfl⟩ := he
        exact x.2
      · intro e he v hv
        exact mem_verts.2 ⟨e, he, hv⟩
      · exact Finset.nonempty_iff_ne_empty.1 hne
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      obtain ⟨hc, h2⟩ := hp
      have hmap : (p.2.subtype (· ∈ G.edgeSet)).map emb = p.2 :=
        Finset.subtype_map_of_mem hc.1
      have hne : p.2.Nonempty := Finset.nonempty_iff_ne_empty.2 h2
      rw [← sep_map_emb emb hf, hmap, ← sep_verts_iff hne, ← eq_verts_of_isConnSub hc hne]
      exact hc.2.2
    · intro X _
      ext x
      simp [emb]
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hc, h2⟩ := hp
      have hmap : (p.2.subtype (· ∈ G.edgeSet)).map emb = p.2 :=
        Finset.subtype_map_of_mem hc.1
      simp only
      rw [hmap, ← eq_verts_of_isConnSub hc (Finset.nonempty_iff_ne_empty.2 h2)]

/-- **Lemma 7.2(b)**, inequality: `c G ≤ F G`. -/
theorem c_le_F [Fintype V] (G : SimpleGraph V) : c G ≤ F G := by
  classical
  rw [c_eq_card_sep]
  unfold F
  apply Finset.card_le_card_of_injOn (fun S => (S, Finset.univ.filter (fun e : Sym2 V =>
    e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S)))
  · intro S hS
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
    refine ⟨fun e he => (Finset.mem_filter.1 he).2.1, fun e he => (Finset.mem_filter.1 he).2.2,
      hS.1, fun A hA hAne hAS => ?_⟩
    obtain ⟨a, ha, b, hb, hbA, hab⟩ := hS.2 A hA hAne hAS
    refine ⟨a, ha, b, hb, hbA, ?_⟩
    rw [fromEdgeSet_adj]
    refine ⟨?_, G.ne_of_adj hab⟩
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    refine ⟨hab, fun v hv => ?_⟩
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact hA ha
    · exact hb
  · intro S _ T _ h
    exact congrArg Prod.fst h

/-- **Lemma 7.2(c)**: adding an edge strictly increases `F`. -/
theorem F_lt_of_adj [Fintype V] {H G : SimpleGraph V} (hHG : H ≤ G) {u v : V} (huv : G.Adj u v)
    (hnot : ¬ H.Adj u v) : F H < F G := by
  classical
  unfold F
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    exact ⟨fun e he => edgeSet_mono hHG (hp.1 e he), hp.2⟩
  · intro hsub
    have hne : u ≠ v := G.ne_of_adj huv
    have hmem : (({u, v} : Finset V), ({s(u, v)} : Finset (Sym2 V))) ∈
        ({p : Finset V × Finset (Sym2 V) | IsConnSub G p.1 p.2} : Finset _) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨by simpa using huv, ?_, ?_⟩
      · intro e he w hw
        rw [Finset.mem_singleton] at he
        subst he
        rcases Sym2.mem_iff.1 hw with rfl | rfl <;> simp
      · have := sep_insert (sep_singleton (fromEdgeSet (((({s(u, v)} : Finset (Sym2 V))) : Set (Sym2 V)))) v)
          (b := u) (by simpa using hne) ⟨v, by simp, by rw [fromEdgeSet_adj]; simp [hne.symm,
            Sym2.eq_swap]⟩
        exact this
    have := hsub hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hnot (by simpa using this.1 _ (Finset.mem_singleton_self _))

/-! ### Forests -/

/-- The edges of `G` with both ends in `S`. -/
noncomputable def indEdges [Fintype V] (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical exact Finset.univ.filter (fun e : Sym2 V => e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S)

theorem mem_indEdges [Fintype V] {G : SimpleGraph V} {S : Finset V} {e : Sym2 V} :
    e ∈ indEdges G S ↔ e ∈ G.edgeSet ∧ ∀ v ∈ e, v ∈ S := by
  classical
  unfold indEdges
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem isConnSub_ind [Fintype V] {G : SimpleGraph V} {S : Finset V} (hS : Sep G S) :
    IsConnSub G S (indEdges G S) := by
  refine ⟨fun e he => (mem_indEdges.1 he).1, fun e he => (mem_indEdges.1 he).2,
    hS.1, fun A hA hAne hAS => ?_⟩
  obtain ⟨a, ha, b, hb, hbA, hab⟩ := hS.2 A hA hAne hAS
  refine ⟨a, ha, b, hb, hbA, ?_⟩
  rw [fromEdgeSet_adj]
  refine ⟨Finset.mem_coe.2 (mem_indEdges.2 ⟨hab, fun v hv => ?_⟩), G.ne_of_adj hab⟩
  rcases Sym2.mem_iff.1 hv with rfl | rfl
  · exact hA ha
  · exact hb

omit [DecidableEq V] in
theorem sep_of_isConnSub {G : SimpleGraph V} {S : Finset V} {E : Finset (Sym2 V)}
    (h : IsConnSub G S E) : Sep G S := by
  refine sep_mono ?_ h.2.2
  intro x y hxy
  rw [fromEdgeSet_adj] at hxy
  exact h.1 _ hxy.1

/-- In a forest, a connected subgraph is induced. -/
theorem eq_indEdges_of_acyclic [Fintype V] {G : SimpleGraph V} (hG : G.IsAcyclic) {S : Finset V}
    {E : Finset (Sym2 V)} (h : IsConnSub G S E) : E = indEdges G S := by
  apply Finset.Subset.antisymm
  · intro e he
    exact mem_indEdges.2 ⟨h.1 e he, h.2.1 e he⟩
  · intro e he
    obtain ⟨heG, hends⟩ := mem_indEdges.1 he
    induction e using Sym2.ind with
    | h a b =>
    by_contra hnot
    have hab : G.Adj a b := heG
    have ha : a ∈ S := hends a (Sym2.mem_mk_left a b)
    have hb : b ∈ S := hends b (Sym2.mem_mk_right a b)
    have hconn : ((fromEdgeSet (E : Set (Sym2 V))).induce (S : Set V)).Connected :=
      (isConnSet_iff_sep _ _).2 h.2.2
    obtain ⟨q⟩ := hconn.preconnected ⟨a, ha⟩ ⟨b, hb⟩
    let q1 := q.map (Embedding.induce (G := fromEdgeSet (E : Set (Sym2 V))) (S : Set V)).toHom
    have hle : fromEdgeSet (E : Set (Sym2 V)) ≤ G := by
      intro x y hxy; rw [fromEdgeSet_adj] at hxy; exact h.1 _ hxy.1
    let q2 : G.Walk a b := q1.mapLe hle
    have hbridge := (isAcyclic_iff_forall_isBridge.1 hG) heG
    have hmem := isBridge_iff_forall_walk_mem_edges.1 hbridge q2
    have hq2 : q2.edges = q1.edges := Walk.edges_mapLe_eq_edges hle q1
    rw [hq2] at hmem
    have := Walk.edges_subset_edgeSet q1 hmem
    rw [edgeSet_fromEdgeSet] at this
    exact hnot this.1

/-- The vertices and edges of a walk form a connected subgraph. -/
theorem sep_walk {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    Sep (fromEdgeSet ((p.edges.toFinset : Finset (Sym2 V)) : Set (Sym2 V))) p.support.toFinset := by
  induction p with
  | nil => simpa using sep_singleton _ _
  | @cons x y z hxy q ih =>
    rw [Walk.edges_cons, Walk.support_cons, List.toFinset_cons, List.toFinset_cons]
    have hmono : fromEdgeSet ((q.edges.toFinset : Finset (Sym2 V)) : Set (Sym2 V)) ≤
        fromEdgeSet (((insert s(x, y) q.edges.toFinset : Finset (Sym2 V))) : Set (Sym2 V)) :=
      fromEdgeSet_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    have ih' := sep_mono hmono ih
    by_cases hx : x ∈ q.support.toFinset
    · rw [Finset.insert_eq_of_mem hx]; exact ih'
    · refine sep_insert ih' hx ⟨y, List.mem_toFinset.2 q.start_mem_support, ?_⟩
      rw [fromEdgeSet_adj]
      refine ⟨by simp [Sym2.eq_swap], (G.ne_of_adj hxy).symm⟩

/-- **Lemma 7.2(b)**: `c G = F G` if and only if `G` is a forest. -/
theorem c_eq_F_iff [Fintype V] (G : SimpleGraph V) : c G = F G ↔ G.IsAcyclic := by
  classical
  constructor
  · intro hcF
    by_contra hcyc
    rw [isAcyclic_iff_forall_isBridge] at hcyc
    push Not at hcyc
    obtain ⟨e, heG, hnb⟩ := hcyc
    induction e using Sym2.ind with
    | h a b =>
    rw [isBridge_iff_forall_walk_mem_edges] at hnb
    push Not at hnb
    obtain ⟨p, hp⟩ := hnb
    have hab : G.Adj a b := heG
    set S := p.support.toFinset
    set E := p.edges.toFinset
    have hpc : IsConnSub G S E := by
      refine ⟨fun e he => p.edges_subset_edgeSet (List.mem_toFinset.1 he), ?_, sep_walk p⟩
      intro e he w hw
      have he' := List.mem_toFinset.1 he
      induction e using Sym2.ind with
      | h x y =>
      rcases Sym2.mem_iff.1 hw with rfl | rfl
      · exact List.mem_toFinset.2 (p.fst_mem_support_of_mem_edges he')
      · exact List.mem_toFinset.2 (p.snd_mem_support_of_mem_edges he')
    -- the injection `S ↦ (S, indEdges G S)` misses `(S, E)`
    have hlt : c G < F G := by
      rw [c_eq_card_sep]
      unfold F
      set I := ({T : Finset V | Sep G T} : Finset (Finset V)).image (fun T => (T, indEdges G T))
      have hIc : #I = #({T : Finset V | Sep G T} : Finset (Finset V)) :=
        Finset.card_image_of_injective _ (fun T T' h => congrArg Prod.fst h)
      rw [← hIc]
      apply Finset.card_lt_card
      refine ⟨?_, ?_⟩
      · intro q hq
        simp only [I, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
        obtain ⟨T, hT, rfl⟩ := hq
        exact isConnSub_ind hT
      · intro hsub
        have hmem : (S, E) ∈ ({p : Finset V × Finset (Sym2 V) | IsConnSub G p.1 p.2} : Finset _) := by
          simpa using hpc
        have := hsub hmem
        simp only [I, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
          Prod.mk.injEq] at this
        obtain ⟨T0, -, hT0S, hTE⟩ := this
        have ha : a ∈ S := List.mem_toFinset.2 p.start_mem_support
        have hb : b ∈ S := List.mem_toFinset.2 p.end_mem_support
        have : s(a, b) ∈ indEdges G S := mem_indEdges.2 ⟨hab, fun v hv => by
          rcases Sym2.mem_iff.1 hv with rfl | rfl
          · exact ha
          · exact hb⟩
        rw [← hT0S, hTE] at this
        exact hp (List.mem_toFinset.1 this)
    omega
  · intro hG
    apply le_antisymm (c_le_F G)
    rw [c_eq_card_sep]
    unfold F
    apply Finset.card_le_card_of_injOn (fun p => p.1)
    · intro p hp
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp ⊢
      exact sep_of_isConnSub hp
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hp hq
      have h1 := eq_indEdges_of_acyclic hG hp
      have h2 := eq_indEdges_of_acyclic hG hq
      simp only at hpq
      rw [hpq] at h1
      exact Prod.ext hpq (h1.trans h2.symm)

end ConnectedSets
