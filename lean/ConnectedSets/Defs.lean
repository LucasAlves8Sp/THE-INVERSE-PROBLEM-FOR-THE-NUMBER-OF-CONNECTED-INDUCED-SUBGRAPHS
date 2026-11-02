/-
ConnectedSets/Defs.lean

The number c(G) of connected sets of a finite simple graph, defined through
Mathlib's notion of connectedness of induced subgraphs, together with
* a combinatorial characterization by separations (`isConnSet_iff_sep`),
* invariance under graph isomorphism (`c_congr`),
* the bounds T(n) ≤ c(G) ≤ 2^n - 1 for connected G on n vertices.
-/
import ConnectedSets.Basic

open Finset

namespace ConnectedSets

variable {V W : Type*}

/-- `S` is a connected set of `G`: the subgraph of `G` induced on `S` is connected.
(Mathlib's `Connected` includes nonemptiness, so connected sets are nonempty.) -/
def IsConnSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  (G.induce (S : Set V)).Connected

open Classical in
/-- `c G` is the number of connected sets of `G` (vertex sets inducing a connected subgraph). -/
noncomputable def c [Fintype V] (G : SimpleGraph V) : ℕ :=
  #{S : Finset V | IsConnSet G S}

/-- Separation form of connectedness of a vertex set: `S` is nonempty, and every nonempty
proper subset `A` of `S` has an edge to `S \ A`. -/
def Sep (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.Nonempty ∧ ∀ A ⊆ S, A.Nonempty → A ≠ S → ∃ a ∈ A, ∃ b ∈ S, b ∉ A ∧ G.Adj a b

theorem isConnSet_iff_sep [DecidableEq V] (G : SimpleGraph V) (S : Finset V) :
    IsConnSet G S ↔ Sep G S := by
  classical
  constructor
  · intro h
    have hne : S.Nonempty := by
      obtain ⟨⟨x, hx⟩⟩ := h.nonempty
      exact ⟨x, hx⟩
    refine ⟨hne, ?_⟩
    intro A hAS hA hAne
    obtain ⟨a, ha⟩ := hA
    have hb : ∃ b ∈ S, b ∉ A := by
      by_contra hcon
      push Not at hcon
      exact hAne (Finset.Subset.antisymm hAS hcon)
    obtain ⟨b, hbS, hbA⟩ := hb
    have hS' : (a ∈ (S : Set V)) := hAS ha
    obtain ⟨p⟩ := h.preconnected ⟨a, hS'⟩ ⟨b, hbS⟩
    obtain ⟨d, -, hd1, hd2⟩ :=
      p.exists_boundary_dart {x : (S : Set V) | x.1 ∈ A} (by simpa using ha) (by simpa using hbA)
    refine ⟨d.fst.1, hd1, d.snd.1, d.snd.2, hd2, ?_⟩
    exact d.adj
  · rintro ⟨hne, hsep⟩
    obtain ⟨x0, hx0⟩ := hne
    have key : ∀ y : (S : Set V), (G.induce (S : Set V)).Reachable ⟨x0, hx0⟩ y := by
      by_contra hcon
      push Not at hcon
      set R : Finset V := S.filter (fun z => ∃ hz : z ∈ S,
        (G.induce (S : Set V)).Reachable ⟨x0, hx0⟩ ⟨z, hz⟩) with hR
      have hRS : R ⊆ S := Finset.filter_subset _ _
      have hRne : R.Nonempty := ⟨x0, by simp [hR, hx0]⟩
      have hRneS : R ≠ S := by
        obtain ⟨y, hy⟩ := hcon
        intro hRS'
        have : y.1 ∈ R := by rw [hRS']; exact y.2
        simp only [hR, Finset.mem_filter] at this
        obtain ⟨-, hz, hreach⟩ := this
        exact hy hreach
      obtain ⟨a, haR, b, hbS, hbR, hab⟩ := hsep R hRS hRne hRneS
      simp only [hR, Finset.mem_filter] at haR
      obtain ⟨-, haS, hreach⟩ := haR
      apply hbR
      simp only [hR, Finset.mem_filter]
      refine ⟨hbS, hbS, hreach.trans ?_⟩
      exact SimpleGraph.Adj.reachable (G := G.induce (S : Set V)) (u := ⟨a, haS⟩) (v := ⟨b, hbS⟩) hab
    have : Nonempty (S : Set V) := ⟨⟨x0, hx0⟩⟩
    exact (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨⟨x0, hx0⟩, key⟩

theorem c_eq_card_sep [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidablePred (Sep G)] :
    c G = #{S : Finset V | Sep G S} := by
  classical
  unfold c
  congr 1
  ext S
  simp [isConnSet_iff_sep]

/-! ### Elementary facts about `Sep` -/

theorem Sep.nonempty {G : SimpleGraph V} {S : Finset V} (h : Sep G S) : S.Nonempty := h.1

theorem sep_singleton (G : SimpleGraph V) (v : V) : Sep G {v} := by
  refine ⟨Finset.singleton_nonempty v, ?_⟩
  intro A hA hAne hAS
  exfalso
  exact hAS ((Finset.subset_singleton_iff.1 hA).resolve_left hAne.ne_empty)

/-- Adding a vertex adjacent to a connected set keeps it connected. -/
theorem sep_insert [DecidableEq V] {G : SimpleGraph V} {P : Finset V} {b : V}
    (hP : Sep G P) (hb : b ∉ P) (hadj : ∃ a ∈ P, G.Adj a b) : Sep G (insert b P) := by
  refine ⟨Finset.insert_nonempty b P, ?_⟩
  intro A hA hAne hAS
  obtain ⟨a0, ha0P, hab0⟩ := hadj
  by_cases hbA : b ∈ A
  · -- b ∈ A
    by_cases hA' : (A.erase b).Nonempty
    · have hA'P : A.erase b ⊆ P := by
        intro x hx
        have hxA := Finset.mem_of_mem_erase hx
        have hxb := Finset.ne_of_mem_erase hx
        rcases Finset.mem_insert.1 (hA hxA) with h | h
        · exact absurd h hxb
        · exact h
      have hA'ne : A.erase b ≠ P := by
        intro heq
        apply hAS
        ext x
        constructor
        · intro hx; exact hA hx
        · intro hx
          rcases Finset.mem_insert.1 hx with h | h
          · rw [h]; exact hbA
          · rw [← heq] at h; exact Finset.mem_of_mem_erase h
      obtain ⟨x, hx, y, hyP, hyA', hxy⟩ := hP.2 _ hA'P hA' hA'ne
      refine ⟨x, Finset.mem_of_mem_erase hx, y, Finset.mem_insert_of_mem hyP, ?_, hxy⟩
      intro hyA
      apply hyA'
      refine Finset.mem_erase.2 ⟨?_, hyA⟩
      rintro rfl
      exact hb hyP
    · -- A = {b}
      have hAb : A = {b} := by
        apply Finset.Subset.antisymm
        · intro x hx
          by_contra hxb
          exact hA' ⟨x, Finset.mem_erase.2 ⟨by simpa using hxb, hx⟩⟩
        · simpa using hbA
      refine ⟨b, hbA, a0, Finset.mem_insert_of_mem ha0P, ?_, hab0.symm⟩
      rw [hAb, Finset.mem_singleton]
      rintro rfl
      exact hb ha0P
  · -- b ∉ A, so A ⊆ P
    have hAP : A ⊆ P := by
      intro x hx
      rcases Finset.mem_insert.1 (hA hx) with h | h
      · exact absurd (h ▸ hx) hbA
      · exact h
    by_cases hAeq : A = P
    · subst hAeq
      exact ⟨a0, ha0P, b, Finset.mem_insert_self b A, hbA, hab0⟩
    · obtain ⟨x, hx, y, hyP, hyA, hxy⟩ := hP.2 A hAP hAne hAeq
      exact ⟨x, hx, y, Finset.mem_insert_of_mem hyP, hyA, hxy⟩

/-- Growth: inside a connected set `S`, a proper connected subset can be enlarged by one vertex. -/
theorem sep_grow [DecidableEq V] {G : SimpleGraph V} {S P : Finset V} (hS : Sep G S)
    (hP : Sep G P) (hPS : P ⊆ S) (hne : P ≠ S) :
    ∃ b ∈ S, b ∉ P ∧ Sep G (insert b P) := by
  obtain ⟨a, ha, b, hbS, hbP, hab⟩ := hS.2 P hPS hP.1 hne
  exact ⟨b, hbS, hbP, sep_insert hP hbP ⟨a, ha, hab⟩⟩

/-- Chains: a connected set `S` containing `r` has, for every `1 ≤ t ≤ #S`, a connected subset of
size `t` containing `r`. -/
theorem exists_sep_card [DecidableEq V] {G : SimpleGraph V} {S : Finset V} (hS : Sep G S)
    {r : V} (hr : r ∈ S) :
    ∀ t, 1 ≤ t → t ≤ #S → ∃ P ⊆ S, Sep G P ∧ r ∈ P ∧ #P = t := by
  intro t ht1 htS
  induction t, ht1 using Nat.le_induction with
  | base => exact ⟨{r}, by simpa using hr, sep_singleton G r, by simp, by simp⟩
  | succ t ht ih =>
    obtain ⟨P, hPS, hP, hrP, hPt⟩ := ih (by omega)
    have hne : P ≠ S := by
      rintro rfl; omega
    obtain ⟨b, hbS, hbP, hsep⟩ := sep_grow hS hP hPS hne
    refine ⟨insert b P, Finset.insert_subset hbS hPS, hsep, Finset.mem_insert_of_mem hrP, ?_⟩
    rw [Finset.card_insert_of_notMem hbP, hPt]

/-! ### Bounds -/

/-- `T n = n(n+1)/2`. -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

theorem T_succ (n : ℕ) : T (n + 1) = T n + (n + 1) := by
  unfold T
  have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + 2 * (n + 1) := by ring
  rw [h, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]

/-- A connected set with `s` elements has at least `T s` connected subsets. -/
theorem T_le_card_sep_subsets [DecidableEq V] (G : SimpleGraph V) [DecidablePred (Sep G)] :
    ∀ s (S : Finset V), Sep G S → #S = s → T s ≤ #{X ∈ S.powerset | Sep G X} := by
  intro s
  induction s with
  | zero => intro S _ _; simp [T]
  | succ s ih =>
    intro S hS hcard
    obtain ⟨r, hr⟩ := hS.1
    -- a connected subset of size s
    rcases Nat.eq_zero_or_pos s with hs0 | hspos
    · subst hs0
      -- S is a singleton; it is a connected subset of itself
      have : 1 ≤ #{X ∈ S.powerset | Sep G X} :=
        Finset.card_pos.2 ⟨S, by simp [hS]⟩
      simpa [T] using this
    obtain ⟨P, hPS, hP, -, hPcard⟩ := exists_sep_card hS hr s hspos (by omega)
    obtain ⟨w, hwS, hwP⟩ : ∃ w ∈ S, w ∉ P := by
      by_contra hcon
      push Not at hcon
      have : S ⊆ P := hcon
      have := Finset.card_le_card this
      omega
    -- family 1: connected subsets of P
    have h1 := ih P hP hPcard
    -- family 2: connected subsets of S containing w, one of each size 1..s+1
    set F2 := {X ∈ S.powerset | Sep G X ∧ w ∈ X} with hF2
    have h2 : s + 1 ≤ #F2 := by
      have hsurj : Finset.Icc 1 (s + 1) ⊆ F2.image Finset.card := by
        intro t ht
        rw [Finset.mem_Icc] at ht
        obtain ⟨X, hXS, hX, hwX, hXt⟩ := exists_sep_card hS hwS t ht.1 (by omega)
        exact Finset.mem_image.2 ⟨X, by simp [hF2, hXS, hX, hwX], hXt⟩
      have := Finset.card_le_card hsurj
      simp only [Nat.card_Icc, add_tsub_cancel_right] at this
      exact this.trans Finset.card_image_le
    -- the two families are disjoint subfamilies of the connected subsets of S
    have hdisj : Disjoint ({X ∈ P.powerset | Sep G X}) F2 := by
      rw [Finset.disjoint_left]
      intro X hX hX2
      simp only [Finset.mem_filter, Finset.mem_powerset, hF2] at hX hX2
      exact hwP (hX.1 hX2.2.2)
    have hsub : ({X ∈ P.powerset | Sep G X}) ∪ F2 ⊆ {X ∈ S.powerset | Sep G X} := by
      intro X hX
      rcases Finset.mem_union.1 hX with h | h
      · simp only [Finset.mem_filter, Finset.mem_powerset] at h ⊢
        exact ⟨h.1.trans hPS, h.2⟩
      · simp only [hF2, Finset.mem_filter, Finset.mem_powerset] at h ⊢
        exact ⟨h.1, h.2.1⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at this
    rw [T_succ]
    omega

/-- `Sep G univ` is the connectedness of `G`. -/
theorem connected_iff_sep_univ [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    G.Connected ↔ Sep G Finset.univ := by
  rw [← isConnSet_iff_sep]
  unfold IsConnSet
  rw [Finset.coe_univ]
  exact (SimpleGraph.Iso.connected_iff (SimpleGraph.induceUnivIso G)).symm

theorem T_le_c [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.Connected) :
    T (Fintype.card V) ≤ c G := by
  classical
  rw [c_eq_card_sep]
  have h := T_le_card_sep_subsets G (Fintype.card V) Finset.univ
    ((connected_iff_sep_univ G).1 hG) Finset.card_univ
  simpa using h

theorem c_le [Fintype V] (G : SimpleGraph V) : c G ≤ 2 ^ Fintype.card V - 1 := by
  classical
  have hsub : ({S : Finset V | IsConnSet G S} : Finset (Finset V)) ⊆ Finset.univ.erase ∅ := by
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    refine Finset.mem_erase.2 ⟨?_, Finset.mem_univ _⟩
    rintro rfl
    obtain ⟨⟨x, hx⟩⟩ := hS.nonempty
    simp at hx
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset] at this
  unfold c
  convert this

/-! ### Invariance under isomorphism -/

theorem sep_map_iff [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H)
    (S : Finset V) : Sep H (S.map φ.toEquiv.toEmbedding) ↔ Sep G S := by
  classical
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨by simpa using hne, ?_⟩
    intro A hA hAne hAS
    obtain ⟨a, ha, b, hb, hbA, hab⟩ := h (A.map φ.toEquiv.toEmbedding) (Finset.map_subset_map.2 hA)
      (by simpa using hAne) (by simpa using hAS)
    simp only [Finset.mem_map] at ha hb hbA
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    refine ⟨a', ha', b', hb', ?_, ?_⟩
    · intro hb'A; exact hbA ⟨b', hb'A, rfl⟩
    · simpa using (φ.map_adj_iff).1 hab
  · rintro ⟨hne, h⟩
    refine ⟨by simpa using hne, ?_⟩
    intro A hA hAne hAS
    set A' := S.filter (fun x => φ x ∈ A) with hA'
    have hA'map : A'.map φ.toEquiv.toEmbedding = A := by
      ext y
      simp only [Finset.mem_map, hA', Finset.mem_filter]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx.2
      · intro hy
        have hyS := hA hy
        simp only [Finset.mem_map] at hyS
        obtain ⟨x, hxS, rfl⟩ := hyS
        exact ⟨x, ⟨hxS, hy⟩, rfl⟩
    have hA'S : A' ⊆ S := Finset.filter_subset _ _
    have hA'ne : A'.Nonempty := by
      rw [← Finset.map_nonempty (f := φ.toEquiv.toEmbedding), hA'map]; exact hAne
    have hA'S' : A' ≠ S := by
      intro heq; apply hAS; rw [← hA'map, heq]
    obtain ⟨a, ha, b, hb, hbA, hab⟩ := h A' hA'S hA'ne hA'S'
    refine ⟨φ a, ?_, φ b, ?_, ?_, φ.map_adj_iff.2 hab⟩
    · simp only [hA', Finset.mem_filter] at ha; exact ha.2
    · exact Finset.mem_map_of_mem _ hb
    · intro hbA'; exact hbA (by simp only [hA', Finset.mem_filter]; exact ⟨hb, hbA'⟩)

theorem c_congr [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} (φ : G ≃g H) : c G = c H := by
  classical
  rw [c_eq_card_sep, c_eq_card_sep]
  apply Finset.card_bij (fun S _ => S.map φ.toEquiv.toEmbedding)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact (sep_map_iff φ S).2 hS
  · intro S _ S' _ h
    exact Finset.map_injective _ h
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
    have hmm : (T.map φ.symm.toEquiv.toEmbedding).map φ.toEquiv.toEmbedding = T := by
      ext y
      simp only [Finset.mem_map, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
        simpa using hz
      · intro hy
        exact ⟨φ.symm y, ⟨y, hy, rfl⟩, by simp⟩
    refine ⟨T.map φ.symm.toEquiv.toEmbedding, ?_, hmm⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← sep_map_iff φ, hmm]
    exact hT

end ConnectedSets
