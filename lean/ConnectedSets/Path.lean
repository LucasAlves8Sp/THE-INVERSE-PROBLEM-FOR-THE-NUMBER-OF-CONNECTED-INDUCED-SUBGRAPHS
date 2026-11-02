/-
ConnectedSets/Path.lean

Proposition 3.2 of the paper and the exact counts behind it:
* `c_eq_T_iff` : a connected graph on `n` vertices has `c = T n` if and only if it is isomorphic to
  the path `pathGraph n`;
* `path_gap` : a connected graph on `n ≥ 4` vertices that is not isomorphic to `pathGraph n` has
  `c ≥ T n + (n - 3)`;
* `c_pathGraph` : `c (pathGraph n) = T n`;
* `c_spiderG` : the spider with legs of lengths `1, 1, n - 3` has `c = T n + (n - 3)`.
-/
import ConnectedSets.Gap
import Mathlib.Combinatorics.SimpleGraph.Hasse

open Finset SimpleGraph

namespace ConnectedSets

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidablePred (Sep G)]

/-- Two distinct connected subsets of `S` of the same size containing `w` force
`AS G S w ≥ #S + 1`. -/
theorem succ_le_AS_of_ne {S X Y : Finset V} (hS : Sep G S) {w : V} (hw : w ∈ S) (hXS : X ⊆ S)
    (hYS : Y ⊆ S) (hX : Sep G X) (hY : Sep G Y) (hwX : w ∈ X) (hwY : w ∈ Y) (hXY : X ≠ Y)
    (hc : #X = #Y) : #S + 1 ≤ AS G S w := by
  unfold AS
  set F := {Z ∈ S.powerset | Sep G Z ∧ w ∈ Z} with hF
  have hXF : X ∈ F := by simp [hF, hXS, hX, hwX]
  have hYF : Y ∈ F.erase X := Finset.mem_erase.2 ⟨Ne.symm hXY, by simp [hF, hYS, hY, hwY]⟩
  have hsurj : Finset.Icc 1 #S ⊆ (F.erase X).image Finset.card := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    by_cases htX : t = #X
    · exact Finset.mem_image.2 ⟨Y, hYF, by rw [htX, hc]⟩
    · obtain ⟨Z, hZS, hZ, hwZ, hZt⟩ := exists_sep_card hS hw t ht.1 ht.2
      refine Finset.mem_image.2 ⟨Z, Finset.mem_erase.2 ⟨?_, by simp [hF, hZS, hZ, hwZ]⟩, hZt⟩
      rintro rfl; exact htX hZt.symm
  have h1 := Finset.card_le_card hsurj
  simp only [Nat.card_Icc, add_tsub_cancel_right] at h1
  have h2 := h1.trans Finset.card_image_le
  rw [Finset.card_erase_of_mem hXF] at h2
  have : 1 ≤ #F := Finset.card_pos.2 ⟨_, hXF⟩
  omega

/-- In the enumeration given by an end, only consecutive vertices are adjacent. -/
theorem no_chord_of_end {S : Finset V} {s : ℕ} {φ : ℕ → V} (hS : Sep G S) (hs : #S = s)
    (hA : AS G S (φ 0) = s) (hφS : ∀ i < s, φ i ∈ S) (hφinj : ∀ i < s, ∀ j < s, φ i = φ j → i = j)
    (hφadj : ∀ i, i + 1 < s → G.Adj (φ i) (φ (i + 1))) :
    ∀ i < s, ∀ j < s, G.Adj (φ i) (φ j) → i + 1 = j ∨ j + 1 = i := by
  -- the case `i + 2 ≤ j`
  have key : ∀ i < s, ∀ j < s, i + 2 ≤ j → ¬ G.Adj (φ i) (φ j) := by
    intro i hi j hj hij hadj
    have h0 : φ 0 ∈ S := hφS 0 (by omega)
    set X := insert (φ j) (Ivl φ 0 i) with hXdef
    set Y := Ivl φ 0 (i + 1) with hYdef
    have hjX : φ j ∉ Ivl φ 0 i := by
      intro h; have := (mem_Ivl_iff hφinj hi hj).1 h; omega
    have hX : Sep G X := sep_insert (sep_Ivl hφadj hφinj i (by omega) hi) hjX
      ⟨φ i, (mem_Ivl_iff hφinj hi hi).2 ⟨by omega, le_rfl⟩, hadj⟩
    have hY : Sep G Y := sep_Ivl hφadj hφinj (i + 1) (by omega) (by omega)
    have hXS : X ⊆ S := Finset.insert_subset (hφS j hj) (Ivl_subset hφS hi)
    have hYS : Y ⊆ S := Ivl_subset hφS (by omega)
    have hcardI : ∀ b, b < s → #(Ivl φ 0 b) = b + 1 := by
      intro b hb
      unfold Ivl
      rw [Finset.card_image_of_injOn, Nat.card_Icc]
      · omega
      intro p hp q hq h
      simp only [Finset.coe_Icc, Set.mem_Icc] at hp hq
      exact hφinj p (by omega) q (by omega) h
    have hc : #X = #Y := by
      rw [hXdef, hYdef, Finset.card_insert_of_notMem hjX, hcardI i hi, hcardI (i + 1) (by omega)]
    have hne : X ≠ Y := by
      intro h
      have : φ j ∈ Y := h ▸ Finset.mem_insert_self _ _
      have := (mem_Ivl_iff hφinj (by omega) hj).1 this
      omega
    have hw0X : φ 0 ∈ X := Finset.mem_insert_of_mem ((mem_Ivl_iff hφinj hi (by omega)).2 ⟨le_rfl,
      by omega⟩)
    have hw0Y : φ 0 ∈ Y := (mem_Ivl_iff hφinj (by omega) (by omega)).2 ⟨le_rfl, by omega⟩
    have := succ_le_AS_of_ne hS h0 hXS hYS hX hY hw0X hw0Y hne hc
    omega
  intro i hi j hj hadj
  by_contra hcon
  push Not at hcon
  have hij : i ≠ j := fun h => G.loopless.irrefl (φ i) (by rw [h] at hadj ⊢; exact hadj)
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact key i hi j hj (by omega) hadj
  · exact key j hj i hi (by omega) hadj.symm

/-- A connected set with the minimum number of connected subsets has an end. -/
theorem exists_end_of_tight {S : Finset V} (hS : Sep G S) (ht : NS G S = T #S) :
    ∃ y ∈ S, AS G S y = #S := by
  by_cases h1 : #S = 1
  · obtain ⟨y, rfl⟩ := Finset.card_eq_one.1 h1
    refine ⟨y, Finset.mem_singleton_self y, ?_⟩
    have := NS_decomp (G := G) {y} y
    rw [Finset.erase_singleton, NS_empty, ht, h1] at this
    rw [h1]; simpa [T] using this.symm
  · have h2 : 2 ≤ #S := by
      have := Finset.card_pos.2 hS.1; omega
    obtain ⟨w, hw, hw'⟩ := exists_noncut hS h2
    exact ⟨w, hw, end_of_tight hS hw hw' ht⟩

/-! ### Graphs -/

theorem c_eq_NS [Fintype V] (G : SimpleGraph V) [DecidablePred (Sep G)] :
    c G = NS G Finset.univ := by
  rw [c_eq_card_sep]
  unfold NS
  rw [Finset.powerset_univ]

/-- **Dichotomy.** A connected graph on `n` vertices has `c = T n` or `c ≥ T n + (n - 3)`. -/
theorem c_gap [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    c G = T (Fintype.card V) ∨ T (Fintype.card V) + (Fintype.card V - 3) ≤ c G := by
  classical
  rw [c_eq_NS G]
  exact NS_gap _ Finset.univ ((connected_iff_sep_univ G).1 hG) Finset.card_univ

/-- A connected graph with `c = T n` is isomorphic to the path on `n` vertices. -/
theorem iso_path_of_tight [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (h : c G = T (Fintype.card V)) : Nonempty (pathGraph (Fintype.card V) ≃g G) := by
  classical
  set n := Fintype.card V with hn
  have hS : Sep G Finset.univ := (connected_iff_sep_univ G).1 hG
  rw [c_eq_NS G] at h
  obtain ⟨y, -, hy⟩ := exists_end_of_tight hS (by rw [Finset.card_univ, ← hn]; exact h)
  rw [Finset.card_univ, ← hn] at hy
  obtain ⟨φ, hφ0, hφS, hφinj, hφsurj, hφadj⟩ :=
    chain_of_end n Finset.univ y hS (Finset.mem_univ y) Finset.card_univ hy
  have hnc := no_chord_of_end hS Finset.card_univ (by rw [hφ0]; exact hy) hφS hφinj hφadj
  let f : Fin n → V := fun i => φ i.val
  have hbij : Function.Bijective f := by
    constructor
    · intro i j hij
      exact Fin.ext (hφinj i.val i.2 j.val j.2 hij)
    · intro v
      obtain ⟨i, hi, hiv⟩ := hφsurj v (Finset.mem_univ v)
      exact ⟨⟨i, hi⟩, hiv⟩
  refine ⟨⟨Equiv.ofBijective f hbij, ?_⟩⟩
  intro a b
  simp only [Equiv.ofBijective_apply, f, pathGraph_adj]
  constructor
  · intro hab
    exact hnc a.val a.2 b.val b.2 hab
  · rintro (hab | hab)
    · have := hφadj a.val (by omega); rwa [hab] at this
    · have := hφadj b.val (by omega); rw [hab] at this; exact this.symm

/-! ### Convex connected sets -/

section convex

variable {n : ℕ} {H : SimpleGraph (Fin n)}

/-- If adjacent vertices of `S` have consecutive values, connected subsets of `S` are convex. -/
theorem mem_of_consec {S X : Finset (Fin n)}
    (hcons : ∀ u ∈ S, ∀ v ∈ S, H.Adj u v → u.val + 1 = v.val ∨ v.val + 1 = u.val) (hXS : X ⊆ S)
    (hX : Sep H X) {a b x : Fin n} (ha : a ∈ X) (hb : b ∈ X) (hax : a ≤ x) (hxb : x ≤ b) :
    x ∈ X := by
  by_contra hx
  set A := X.filter (fun v => v < x) with hA
  have haA : a ∈ A := by
    simp only [hA, Finset.mem_filter]
    exact ⟨ha, lt_of_le_of_ne hax (fun h => hx (h ▸ ha))⟩
  have hAX : A ⊆ X := Finset.filter_subset _ _
  have hbA : b ∉ A := by simp [hA, not_lt.2 hxb]
  obtain ⟨a', ha', b', hb', hb'A, hadj⟩ := hX.2 A hAX ⟨a, haA⟩ (fun h => hbA (h ▸ hb))
  simp only [hA, Finset.mem_filter, not_and, not_lt] at ha' hb'A
  have h1 : x ≤ b' := hb'A hb'
  have h2 : x ≠ b' := fun h => hx (h ▸ hb')
  have h3 : x < b' := lt_of_le_of_ne h1 h2
  have h4 : a' < x := ha'.2
  have := hcons a' (hXS ha'.1) b' (hXS hb') hadj
  have h3' : x.val < b'.val := h3
  have h4' : a'.val < x.val := h4
  omega

/-- Convex connected sets are determined by their least and greatest elements. -/
theorem eq_of_consec {S X Y : Finset (Fin n)}
    (hcons : ∀ u ∈ S, ∀ v ∈ S, H.Adj u v → u.val + 1 = v.val ∨ v.val + 1 = u.val) (hXS : X ⊆ S)
    (hYS : Y ⊆ S) (hX : Sep H X) (hY : Sep H Y)
    (hmin : X.min' hX.1 = Y.min' hY.1) (hmax : X.max' hX.1 = Y.max' hY.1) : X = Y := by
  have key : ∀ (P Q : Finset (Fin n)) (hP : Sep H P) (hQ : Sep H Q), P ⊆ S → Q ⊆ S →
      P.min' hP.1 = Q.min' hQ.1 → P.max' hP.1 = Q.max' hQ.1 → P ⊆ Q := by
    intro P Q hP hQ hPS hQS h1 h2 v hv
    refine mem_of_consec hcons hQS hQ (Q.min'_mem hQ.1) (Q.max'_mem hQ.1) ?_ ?_
    · rw [← h1]; exact P.min'_le v hv
    · rw [← h2]; exact P.le_max' v hv
  exact Finset.Subset.antisymm (key X Y hX hY hXS hYS hmin hmax)
    (key Y X hY hX hYS hXS hmin.symm hmax.symm)

end convex

/-! ### The path -/

theorem c_pathGraph (n : ℕ) : c (pathGraph n) = T n := by
  classical
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have : c (pathGraph 0) = 0 := by
      have := c_le (pathGraph 0); simpa using this
    rw [this]; rfl
  have hconn : (pathGraph n).Connected := connected_pathGraph.2 (by omega)
  have hS : Sep (pathGraph n) Finset.univ := (connected_iff_sep_univ _).1 hconn
  have hcons : ∀ u ∈ (Finset.univ : Finset (Fin n)), ∀ v ∈ (Finset.univ : Finset (Fin n)),
      (pathGraph n).Adj u v → u.val + 1 = v.val ∨ v.val + 1 = u.val :=
    fun u _ v _ h => pathGraph_adj.1 h
  set z : Fin n := ⟨0, hpos⟩
  -- `z` is an end
  have hA : AS (pathGraph n) Finset.univ z ≤ n := by
    unfold AS
    rw [Finset.powerset_univ]
    have := Finset.card_le_card_of_injOn
      (s := ({X | Sep (pathGraph n) X ∧ z ∈ X} : Finset (Finset (Fin n))))
      (t := Finset.range n)
      (fun X => if h : X.Nonempty then (X.max' h).val else 0) ?_ ?_
    · simpa using this
    · intro X _
      simp only [Finset.coe_range, Set.mem_Iio]
      split_ifs <;> omega
    · intro X hX Y hY hXY
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hX hY
      simp only [hX.1.1, hY.1.1, dite_true] at hXY
      apply eq_of_consec hcons (Finset.subset_univ X) (Finset.subset_univ Y) hX.1 hY.1
      · have h1 : X.min' hX.1.1 = z := le_antisymm (X.min'_le z hX.2) (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
        have h2 : Y.min' hY.1.1 = z := le_antisymm (Y.min'_le z hY.2) (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
        rw [h1, h2]
      · exact Fin.ext hXY
  have hA' := card_le_AS hS (Finset.mem_univ z)
  rw [Finset.card_univ, Fintype.card_fin] at hA'
  have := NS_eq_T_of_end n Finset.univ z hS (Finset.mem_univ z)
    (by rw [Finset.card_univ, Fintype.card_fin]) (by omega)
  rw [c_eq_NS, this]

/-- A connected graph on `n` vertices has `c = T n` if and only if it is a path. -/
theorem c_eq_T_iff [Fintype V] (G : SimpleGraph V) (hG : G.Connected) :
    c G = T (Fintype.card V) ↔ Nonempty (pathGraph (Fintype.card V) ≃g G) := by
  classical
  refine ⟨iso_path_of_tight G hG, ?_⟩
  rintro ⟨e⟩
  rw [← c_congr e, c_pathGraph]

/-- **Proposition 3.2.** A connected graph on `n ≥ 4` vertices that is not a path has at least
`T n + (n - 3)` connected sets. -/
theorem path_gap [Fintype V] (G : SimpleGraph V) (hG : G.Connected)
    (hP : IsEmpty (pathGraph (Fintype.card V) ≃g G)) :
    T (Fintype.card V) + (Fintype.card V - 3) ≤ c G := by
  rcases c_gap G hG with h | h
  · exact absurd ((c_eq_T_iff G hG).1 h) (not_nonempty_iff.2 hP)
  · exact h

end ConnectedSets
