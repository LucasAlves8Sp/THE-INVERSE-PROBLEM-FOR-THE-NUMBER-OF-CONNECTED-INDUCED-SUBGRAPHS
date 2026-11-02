/-
ConnectedSets/Glue.lean

Lemma 2.1(c) of the paper (gluing at a vertex), stated inside one graph `G`: the vertex set
`A ∪ B` is covered by two sets meeting only in `v`, with no edge between `A \ {v}` and `B \ {v}`.
Then the graphs `G[A]` and `G[B]` play the roles of `G₁` and `G₂`, and
  `c(G[A ∪ B]) = c_v(G[A]) · c_v(G[B]) + c(G[A] - v) + c(G[B] - v)`,
that is, `NS G (A ∪ B) = AS G A v * AS G B v + NS G (A.erase v) + NS G (B.erase v)`.
The graph form is `c_glue`.
-/
import ConnectedSets.Gap

open Finset

namespace ConnectedSets

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

omit [DecidableEq V] in
/-- The union of two connected sets with a common element is connected. -/
theorem sep_union_of_mem {Y Z : Finset V} [DecidableEq V] (hY : Sep G Y) (hZ : Sep G Z) {v : V}
    (hvY : v ∈ Y) (hvZ : v ∈ Z) : Sep G (Y ∪ Z) := by
  refine ⟨⟨v, Finset.mem_union_left _ hvY⟩, fun P hP hPne hPYZ => ?_⟩
  by_cases h1 : (P ∩ Y).Nonempty ∧ P ∩ Y ≠ Y
  · obtain ⟨a, ha, b, hb, hbP, hab⟩ :=
      hY.2 (P ∩ Y) Finset.inter_subset_right h1.1 h1.2
    exact ⟨a, (Finset.mem_inter.1 ha).1, b, Finset.mem_union_left _ hb,
      fun h => hbP (Finset.mem_inter.2 ⟨h, hb⟩), hab⟩
  by_cases h2 : (P ∩ Z).Nonempty ∧ P ∩ Z ≠ Z
  · obtain ⟨a, ha, b, hb, hbP, hab⟩ :=
      hZ.2 (P ∩ Z) Finset.inter_subset_right h2.1 h2.2
    exact ⟨a, (Finset.mem_inter.1 ha).1, b, Finset.mem_union_right _ hb,
      fun h => hbP (Finset.mem_inter.2 ⟨h, hb⟩), hab⟩
  exfalso
  have hY' : P ∩ Y = ∅ ∨ Y ⊆ P := by
    by_cases h : (P ∩ Y).Nonempty
    · right
      have : P ∩ Y = Y := by by_contra hc; exact h1 ⟨h, hc⟩
      rw [← this]; exact Finset.inter_subset_left
    · left; exact Finset.not_nonempty_iff_eq_empty.1 h
  have hZ' : P ∩ Z = ∅ ∨ Z ⊆ P := by
    by_cases h : (P ∩ Z).Nonempty
    · right
      have : P ∩ Z = Z := by by_contra hc; exact h2 ⟨h, hc⟩
      rw [← this]; exact Finset.inter_subset_left
    · left; exact Finset.not_nonempty_iff_eq_empty.1 h
  rcases hY' with hY' | hY' <;> rcases hZ' with hZ' | hZ'
  · obtain ⟨p, hp⟩ := hPne
    rcases Finset.mem_union.1 (hP hp) with h | h
    · have : p ∈ P ∩ Y := Finset.mem_inter.2 ⟨hp, h⟩
      rw [hY'] at this; simp at this
    · have : p ∈ P ∩ Z := Finset.mem_inter.2 ⟨hp, h⟩
      rw [hZ'] at this; simp at this
  · have : v ∈ P ∩ Y := Finset.mem_inter.2 ⟨hZ' hvZ, hvY⟩
    rw [hY'] at this; simp at this
  · have : v ∈ P ∩ Z := Finset.mem_inter.2 ⟨hY' hvY, hvZ⟩
    rw [hZ'] at this; simp at this
  · exact hPYZ (Finset.Subset.antisymm hP (Finset.union_subset hY' hZ'))

/-- A connected subset of `A ∪ B` meeting both, with no edge between `A` and `B`, is impossible. -/
theorem sub_or_sub {A B X : Finset V} (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hX : Sep G X) (hXAB : X ⊆ A ∪ B) : X ⊆ A ∨ X ⊆ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hA, hB⟩ := hcon
  obtain ⟨b, hbX, hbA⟩ := Finset.not_subset.1 hA
  obtain ⟨a, haX, haB⟩ := Finset.not_subset.1 hB
  have haA : a ∈ A := (Finset.mem_union.1 (hXAB haX)).resolve_right haB
  set P := X.filter (· ∈ A) with hP
  obtain ⟨p, hp, q, hq, hqP, hpq⟩ := hX.2 P (Finset.filter_subset _ _) ⟨a, by simp [hP, haX, haA]⟩
    (fun h => hbA (by have : b ∈ P := h ▸ hbX; simp [hP] at this; exact this.2))
  simp only [hP, Finset.mem_filter, not_and] at hp hqP
  have hqB : q ∈ B := (Finset.mem_union.1 (hXAB hq)).resolve_left (hqP hq)
  exact hno p hp.2 q hqB hpq

theorem NS_union_disjoint {A B : Finset V} [DecidablePred (Sep G)] (hdisj : Disjoint A B)
    (hno : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) : NS G (A ∪ B) = NS G A + NS G B := by
  unfold NS
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext X
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_union]
    constructor
    · rintro ⟨hXAB, hX⟩
      rcases sub_or_sub hno hX hXAB with h | h
      · exact Or.inl ⟨h, hX⟩
      · exact Or.inr ⟨h, hX⟩
    · rintro (⟨h, hX⟩ | ⟨h, hX⟩)
      · exact ⟨h.trans Finset.subset_union_left, hX⟩
      · exact ⟨h.trans Finset.subset_union_right, hX⟩
  · rw [Finset.disjoint_left]
    intro X h1 h2
    simp only [Finset.mem_filter, Finset.mem_powerset] at h1 h2
    obtain ⟨x, hx⟩ := h1.2.1
    exact Finset.disjoint_left.1 hdisj (h1.1 hx) (h2.1 hx)

/-- The trace on `A` of a connected set containing the cut vertex `v` is connected. -/
theorem sep_inter_of_cut {A B X : Finset V} {v : V} (hAB : A ∩ B = {v})
    (hno : ∀ a ∈ A, ∀ b ∈ B, a ≠ v → b ≠ v → ¬ G.Adj a b) (hX : Sep G X) (hXAB : X ⊆ A ∪ B)
    (hvX : v ∈ X) : Sep G (X ∩ A) := by
  have hvA : v ∈ A := (Finset.mem_inter.1 (hAB ▸ Finset.mem_singleton_self v : v ∈ A ∩ B)).1
  have hvB : v ∈ B := (Finset.mem_inter.1 (hAB ▸ Finset.mem_singleton_self v : v ∈ A ∩ B)).2
  refine ⟨⟨v, Finset.mem_inter.2 ⟨hvX, hvA⟩⟩, fun P hP hPne hPne' => ?_⟩
  by_cases hvP : v ∈ P
  · -- enlarge `P` by the part of `X` in `B`
    obtain ⟨y, hyXA, hyP⟩ : ∃ y ∈ X ∩ A, y ∉ P := by
      by_contra hc; push Not at hc; exact hPne' (Finset.Subset.antisymm hP hc)
    have hyv : y ≠ v := fun h => hyP (h ▸ hvP)
    have hyB : y ∉ B := fun h => hyv (by
      have : y ∈ A ∩ B := Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hyXA).2, h⟩
      rw [hAB] at this; exact Finset.mem_singleton.1 this)
    set P' := P ∪ (X ∩ B) with hP'
    have hP'X : P' ⊆ X := Finset.union_subset (hP.trans Finset.inter_subset_left)
      Finset.inter_subset_left
    have hyP' : y ∉ P' := by
      simp only [hP', Finset.mem_union, Finset.mem_inter, not_or, not_and]
      exact ⟨hyP, fun _ => hyB⟩
    obtain ⟨p, hp, q, hqX, hqP', hpq⟩ := hX.2 P' hP'X ⟨v, Finset.mem_union_left _ hvP⟩
      (fun h => hyP' (h ▸ (Finset.mem_inter.1 hyXA).1))
    simp only [hP', Finset.mem_union, Finset.mem_inter, not_or, not_and] at hp hqP'
    have hqB : q ∉ B := hqP'.2 hqX
    have hqA : q ∈ A := (Finset.mem_union.1 (hXAB hqX)).resolve_right hqB
    have hqv : q ≠ v := fun h => hqB (h ▸ hvB)
    rcases hp with hp | ⟨hpX, hpB⟩
    · exact ⟨p, hp, q, Finset.mem_inter.2 ⟨hqX, hqA⟩, hqP'.1, hpq⟩
    · by_cases hpv : p = v
      · subst hpv
        exact ⟨p, hvP, q, Finset.mem_inter.2 ⟨hqX, hqA⟩, hqP'.1, hpq⟩
      · exact absurd hpq.symm (hno q hqA p hpB hqv hpv)
  · have hPX : P ⊆ X := hP.trans Finset.inter_subset_left
    obtain ⟨p, hp, q, hqX, hqP, hpq⟩ := hX.2 P hPX hPne (fun h => hvP (h ▸ hvX))
    have hpA : p ∈ A := (Finset.mem_inter.1 (hP hp)).2
    have hpv : p ≠ v := fun h => hvP (h ▸ hp)
    refine ⟨p, hp, q, Finset.mem_inter.2 ⟨hqX, ?_⟩, hqP, hpq⟩
    rcases Finset.mem_union.1 (hXAB hqX) with h | h
    · exact h
    · by_cases hqv : q = v
      · rw [hqv]; exact hvA
      · exact absurd hpq (hno p hpA q h hpv hqv)

/-- **Lemma 2.1(c)**, inside one graph. -/
theorem NS_glue [DecidablePred (Sep G)] {A B : Finset V} {v : V} (hAB : A ∩ B = {v})
    (hno : ∀ a ∈ A, ∀ b ∈ B, a ≠ v → b ≠ v → ¬ G.Adj a b) :
    NS G (A ∪ B) = AS G A v * AS G B v + NS G (A.erase v) + NS G (B.erase v) := by
  have hvA : v ∈ A := (Finset.mem_inter.1 (hAB ▸ Finset.mem_singleton_self v : v ∈ A ∩ B)).1
  have hvB : v ∈ B := (Finset.mem_inter.1 (hAB ▸ Finset.mem_singleton_self v : v ∈ A ∩ B)).2
  have hAinter : ∀ x ∈ A, x ∈ B → x = v := fun x hxA hxB => by
    have : x ∈ A ∩ B := Finset.mem_inter.2 ⟨hxA, hxB⟩
    rw [hAB] at this; exact Finset.mem_singleton.1 this
  rw [NS_decomp (G := G) (A ∪ B) v]
  have herase : (A ∪ B).erase v = A.erase v ∪ B.erase v := Finset.erase_union_distrib _ _ _
  have hdisj : Disjoint (A.erase v) (B.erase v) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_erase.1 hxA).1 (hAinter x (Finset.mem_of_mem_erase hxA)
      (Finset.mem_of_mem_erase hxB))
  rw [herase, NS_union_disjoint hdisj (fun a ha b hb => hno a (Finset.mem_of_mem_erase ha) b
    (Finset.mem_of_mem_erase hb) (Finset.mem_erase.1 ha).1 (Finset.mem_erase.1 hb).1)]
  have hAS : AS G (A ∪ B) v = AS G A v * AS G B v := by
    unfold AS
    rw [← Finset.card_product]
    apply Finset.card_nbij' (fun X => (X ∩ A, X ∩ B)) (fun p => p.1 ∪ p.2)
    · intro X hX
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hX
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_powerset,
        Set.mem_ofPred_eq]
      have hAB' : A ∩ B = {v} := hAB
      refine ⟨⟨Finset.inter_subset_right, sep_inter_of_cut hAB hno hX.2.1 hX.1 hX.2.2,
        Finset.mem_inter.2 ⟨hX.2.2, hvA⟩⟩, ⟨Finset.inter_subset_right, ?_,
        Finset.mem_inter.2 ⟨hX.2.2, hvB⟩⟩⟩
      have hBA : B ∩ A = {v} := by rw [Finset.inter_comm]; exact hAB'
      refine sep_inter_of_cut hBA (fun a ha b hb hav hbv => fun h => hno b hb a ha hbv hav h.symm)
        hX.2.1 (by rw [Finset.union_comm]; exact hX.1) hX.2.2
    · intro p hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_powerset,
        Set.mem_ofPred_eq] at hp
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq]
      exact ⟨Finset.union_subset_union hp.1.1 hp.2.1, sep_union_of_mem hp.1.2.1 hp.2.2.1
        hp.1.2.2 hp.2.2.2, Finset.mem_union_left _ hp.1.2.2⟩
    · intro X hX
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hX
      show X ∩ A ∪ X ∩ B = X
      rw [← Finset.inter_union_distrib_left]
      exact Finset.inter_eq_left.2 hX.1
    · intro p hp
      simp only [Finset.coe_product, Set.mem_prod, Finset.coe_filter, Finset.mem_powerset,
        Set.mem_ofPred_eq] at hp
      obtain ⟨⟨h1A, -, hv1⟩, ⟨h2B, -, hv2⟩⟩ := hp
      ext1
      · simp only
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 h1A]
        apply Finset.union_eq_left.2
        intro x hx
        obtain ⟨hx2, hxA⟩ := Finset.mem_inter.1 hx
        rw [hAinter x hxA (h2B hx2)]; exact hv1
      · simp only
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.2 h2B]
        apply Finset.union_eq_right.2
        intro x hx
        obtain ⟨hx1, hxB⟩ := Finset.mem_inter.1 hx
        rw [hAinter x (h1A hx1) hxB]; exact hv2
  rw [hAS]
  ring

/-- **Lemma 2.1(c)**: `G` is covered by `A` and `B` with `A ∩ B = {v}` and no edge between
`A \ {v}` and `B \ {v}`; `G[A]` and `G[B]` play the roles of `G₁` and `G₂`. -/
theorem c_glue [Fintype V] [DecidablePred (Sep G)] {A B : Finset V} {v : V} (hcov : A ∪ B = Finset.univ)
    (hAB : A ∩ B = {v}) (hno : ∀ a ∈ A, ∀ b ∈ B, a ≠ v → b ≠ v → ¬ G.Adj a b) :
    c G = AS G A v * AS G B v + NS G (A.erase v) + NS G (B.erase v) := by
  rw [c_eq_card_sep, ← NS_glue hAB hno, hcov]
  unfold NS
  rw [Finset.powerset_univ]

end ConnectedSets
