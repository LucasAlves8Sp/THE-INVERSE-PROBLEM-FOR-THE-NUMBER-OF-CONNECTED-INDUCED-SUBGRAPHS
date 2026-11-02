/-
ConnectedSets/Spider.lean

The spider with legs of lengths `1, 1, n - 3` (equality case of Proposition 3.2):
the path `0 - 1 - ⋯ - (n-2)` with the extra vertex `n - 1` joined to `1`.
* `spiderG_connected`, `c_spiderG : c (spiderG n) = T n + (n - 3)` for `n ≥ 4`.
-/
import ConnectedSets.Path

open Finset SimpleGraph

namespace ConnectedSets

/-- The spider with legs `1, 1, n - 3`, on `Fin n`. -/
def spiderG (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => (u.val + 1 = v.val ∧ v.val + 2 ≤ n) ∨ (u.val = 1 ∧ v.val + 1 = n))

instance (n : ℕ) : DecidableRel (spiderG n).Adj := by
  unfold spiderG; infer_instance

theorem spiderG_adj {n : ℕ} {u v : Fin n} : (spiderG n).Adj u v ↔ u ≠ v ∧
    (((u.val + 1 = v.val ∧ v.val + 2 ≤ n) ∨ (u.val = 1 ∧ v.val + 1 = n)) ∨
     ((v.val + 1 = u.val ∧ u.val + 2 ≤ n) ∨ (v.val = 1 ∧ u.val + 1 = n))) := by
  unfold spiderG; rw [SimpleGraph.fromRel_adj]

/-- The enumeration `i ↦ i` of `Fin n`. -/
def idx (n : ℕ) (hn : 4 ≤ n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt _ (by omega)⟩

theorem idx_val {n : ℕ} (hn : 4 ≤ n) {i : ℕ} (hi : i < n) : (idx n hn i).val = i :=
  Nat.mod_eq_of_lt hi

section

variable {n : ℕ} (hn : 4 ≤ n)
include hn

theorem sep_spider_H : Sep (spiderG n) (Finset.univ.erase ⟨n - 1, by omega⟩) := by
  classical
  have hadj : ∀ i, i + 1 < n - 1 → (spiderG n).Adj (idx n hn i) (idx n hn (i + 1)) := by
    intro i hi
    rw [spiderG_adj, idx_val hn (by omega), idx_val hn (by omega)]
    refine ⟨fun h => ?_, Or.inl (Or.inl ⟨rfl, by omega⟩)⟩
    have := congrArg Fin.val h
    rw [idx_val hn (by omega), idx_val hn (by omega)] at this
    omega
  have hinj : ∀ i < n - 1, ∀ j < n - 1, idx n hn i = idx n hn j → i = j := by
    intro i hi j hj h
    have := congrArg Fin.val h
    rwa [idx_val hn (by omega), idx_val hn (by omega)] at this
  have heq : Finset.univ.erase (⟨n - 1, by omega⟩ : Fin n) = Ivl (idx n hn) 0 (n - 2) := by
    ext v
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Ivl, Finset.mem_image, Finset.mem_Icc]
    constructor
    · intro hv
      refine ⟨v.val, ⟨Nat.zero_le _, ?_⟩, Fin.ext (idx_val hn v.2)⟩
      have : v.val ≠ n - 1 := fun h => hv (Fin.ext h)
      have := v.2
      omega
    · rintro ⟨i, hi, rfl⟩ h
      have := congrArg Fin.val h
      rw [idx_val hn (by omega)] at this
      simp at this
      omega
  rw [heq]
  exact sep_Ivl hadj hinj (n - 2) (by omega) (by omega)

theorem spiderG_connected : (spiderG n).Connected := by
  classical
  rw [connected_iff_sep_univ]
  have hH := sep_spider_H hn
  have heq : (Finset.univ : Finset (Fin n)) =
      insert ⟨n - 1, by omega⟩ (Finset.univ.erase ⟨n - 1, by omega⟩) :=
    (Finset.insert_erase (Finset.mem_univ _)).symm
  rw [heq]
  refine sep_insert hH (Finset.notMem_erase _ _) ⟨⟨1, by omega⟩, ?_, ?_⟩
  · simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.mk.injEq]; omega
  · rw [spiderG_adj]
    exact ⟨by simp only [ne_eq, Fin.mk.injEq]; omega, Or.inl (Or.inr ⟨rfl, show n - 1 + 1 = n by omega⟩)⟩

theorem c_spiderG : c (spiderG n) = T n + (n - 3) := by
  classical
  set G := spiderG n
  set b : Fin n := ⟨n - 1, by omega⟩ with hb
  set one : Fin n := ⟨1, by omega⟩ with hone
  set z : Fin n := ⟨0, by omega⟩ with hz
  set H := (Finset.univ : Finset (Fin n)).erase b with hH
  have hSH : Sep G H := sep_spider_H hn
  have hS : Sep G Finset.univ := (connected_iff_sep_univ G).1 (spiderG_connected hn)
  have hHc : #H = n - 1 := by rw [hH, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin]
  have hcons : ∀ u ∈ H, ∀ v ∈ H, G.Adj u v → u.val + 1 = v.val ∨ v.val + 1 = u.val := by
    intro u hu v hv huv
    have hu' : u.val ≠ n - 1 := fun h => (Finset.mem_erase.1 hu).1 (Fin.ext h)
    have hv' : v.val ≠ n - 1 := fun h => (Finset.mem_erase.1 hv).1 (Fin.ext h)
    rw [spiderG_adj] at huv
    omega
  -- upper bound for `NS G H`: `z` is an end of `H`
  have hzH : z ∈ H := by simp [hH, hb, hz]; omega
  have hAz : AS G H z ≤ n - 1 := by
    unfold AS
    have := Finset.card_le_card_of_injOn
      (s := ({X ∈ H.powerset | Sep G X ∧ z ∈ X} : Finset (Finset (Fin n))))
      (t := Finset.range (n - 1))
      (fun X => if h : X.Nonempty then (X.max' h).val else 0) ?_ ?_
    · simpa using this
    · intro X hX
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hX
      simp only [Finset.coe_range, Set.mem_Iio, hX.2.1.1, dite_true]
      have hm := hX.1 (X.max'_mem hX.2.1.1)
      have : (X.max' hX.2.1.1).val ≠ n - 1 := fun h => (Finset.mem_erase.1 hm).1 (Fin.ext h)
      have := (X.max' hX.2.1.1).2
      omega
    · intro X hX Y hY hXY
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hX hY
      simp only [hX.2.1.1, hY.2.1.1, dite_true] at hXY
      apply eq_of_consec hcons hX.1 hY.1 hX.2.1 hY.2.1
      · have h1 : X.min' hX.2.1.1 = z :=
          le_antisymm (X.min'_le z hX.2.2) (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
        have h2 : Y.min' hY.2.1.1 = z :=
          le_antisymm (Y.min'_le z hY.2.2) (Fin.le_iff_val_le_val.2 (Nat.zero_le _))
        rw [h1, h2]
      · exact Fin.ext hXY
  have hAz' := card_le_AS hSH hzH
  have hNH : NS G H = T (n - 1) := NS_eq_T_of_end (n - 1) H z hSH hzH hHc (by omega)
  -- the pendant vertex `b`
  have hbone : G.Adj b one := by
    rw [spiderG_adj]
    refine ⟨by simp only [hb, hone, ne_eq, Fin.mk.injEq]; omega, Or.inr (Or.inr ⟨rfl, by simp [hb]; omega⟩)⟩
  have huniq : ∀ x ∈ (Finset.univ : Finset (Fin n)), G.Adj b x → x = one := by
    intro x _ hx
    rw [spiderG_adj] at hx
    simp only [hb] at hx
    apply Fin.ext
    have := x.2
    simp only [hone]
    omega
  obtain ⟨-, hAb⟩ := AS_pendant hS (Finset.mem_univ b) (Finset.mem_univ one) hbone huniq
  -- upper bound for the connected subsets of `H` containing `one`
  have hoH : one ∈ H := by simp [hH, hb, hone]; omega
  have hAone : AS G H one ≤ 2 * (n - 2) := by
    unfold AS
    have := Finset.card_le_card_of_injOn
      (s := ({X ∈ H.powerset | Sep G X ∧ one ∈ X} : Finset (Finset (Fin n))))
      (t := ({0, 1} : Finset ℕ) ×ˢ Finset.Icc 1 (n - 2))
      (fun X => (if h : X.Nonempty then (X.min' h).val else 0,
        if h : X.Nonempty then (X.max' h).val else 0)) ?_ ?_
    · rw [Finset.card_product, Nat.card_Icc] at this
      simp only [Finset.mem_singleton, zero_ne_one, not_false_eq_true, Finset.card_insert_of_notMem,
        Finset.card_singleton] at this
      have e : n - 2 + 1 - 1 = n - 2 := by omega
      rw [e] at this
      exact this
    · intro X hX
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hX
      simp only [Finset.coe_product, Set.mem_prod, hX.2.1.1, dite_true, Finset.coe_insert,
        Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff, Finset.coe_Icc,
        Set.mem_Icc]
      have h1 : X.min' hX.2.1.1 ≤ one := X.min'_le one hX.2.2
      have h2 : one ≤ X.max' hX.2.1.1 := X.le_max' one hX.2.2
      have hm := hX.1 (X.max'_mem hX.2.1.1)
      have h3 : (X.max' hX.2.1.1).val ≠ n - 1 := fun h => (Finset.mem_erase.1 hm).1 (Fin.ext h)
      have h4 := (X.max' hX.2.1.1).2
      rw [Fin.le_iff_val_le_val] at h1 h2
      simp only [hone] at h1 h2
      omega
    · intro X hX Y hY hXY
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_ofPred_eq] at hX hY
      simp only [hX.2.1.1, hY.2.1.1, dite_true, Prod.mk.injEq] at hXY
      exact eq_of_consec hcons hX.1 hY.1 hX.2.1 hY.2.1 (Fin.ext hXY.1) (Fin.ext hXY.2)
  -- the count
  have hT : T n = T (n - 1) + n := by
    have e : n = (n - 1) + 1 := by omega
    conv_lhs => rw [e]
    rw [T_succ, ← e]
  have hup : c G ≤ T n + (n - 3) := by
    rw [c_eq_NS G, NS_decomp (G := G) Finset.univ b, hAb, ← hH, hNH]
    omega
  -- lower bound: the spider is not a path
  rcases c_gap G (spiderG_connected hn) with h | h
  · exfalso
    rw [Fintype.card_fin] at h
    obtain ⟨ψ⟩ := iso_path_of_tight G (spiderG_connected hn) (by rw [Fintype.card_fin]; exact h)
    set two : Fin n := ⟨2, by omega⟩ with htwo
    have hadj1 : G.Adj one z := by
      rw [spiderG_adj]; exact ⟨by simp [hone, hz], Or.inr (Or.inl ⟨by simp [hone, hz], by simp [hone]; omega⟩)⟩
    have hadj2 : G.Adj one two := by
      rw [spiderG_adj]; exact ⟨by simp [hone, htwo], Or.inl (Or.inl ⟨by simp [hone, htwo], by simp [htwo]; omega⟩)⟩
    have p0 := pathGraph_adj.1 ((ψ.symm.map_adj_iff).2 hadj1)
    have p2 := pathGraph_adj.1 ((ψ.symm.map_adj_iff).2 hadj2)
    have pb := pathGraph_adj.1 ((ψ.symm.map_adj_iff).2 hbone.symm)
    have d1 : (ψ.symm z).val ≠ (ψ.symm two).val := fun h =>
      (by simp [hz, htwo] : z ≠ two) (ψ.symm.injective (Fin.ext h))
    have d2 : (ψ.symm z).val ≠ (ψ.symm b).val := fun h =>
      (by simp [hz, hb]; omega : z ≠ b) (ψ.symm.injective (Fin.ext h))
    have d3 : (ψ.symm two).val ≠ (ψ.symm b).val := fun h =>
      (by simp [htwo, hb]; omega : two ≠ b) (ψ.symm.injective (Fin.ext h))
    omega
  · rw [Fintype.card_fin] at h
    omega

end

end ConnectedSets
