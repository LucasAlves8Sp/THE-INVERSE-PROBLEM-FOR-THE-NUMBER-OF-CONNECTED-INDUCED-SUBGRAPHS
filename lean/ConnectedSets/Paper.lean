/-
ConnectedSets/Paper.lean

The results of the paper "The inverse problem for the number of connected induced subgraphs",
stated with the paper's numbering. Each statement is proved by the corresponding theorem of the
library; this file only collects them.

Notation of the paper and of the library:
* `c G` : the number of connected sets of `G` (`ConnectedSets.c`);
* `InV m k` : `k ∈ V_m`, i.e. some connected graph on `Fin m` has `c = k`;
* `InLam m k` : `k ∈ Λ_m`, i.e. some graph on `Fin m` has `c = k`;
* `T n = n (n + 1) / 2`;
* `minOrder k = if k = 25 then 6 else Nat.log 2 k + 1`.
-/
import ConnectedSets.Extras
import ConnectedSets.LineGraph
import ConnectedSets.Glue

open Finset SimpleGraph

namespace ConnectedSets.Paper

open ConnectedSets

/-! ### Section 1 -/

/-- **Theorem 1.1.** -/
theorem theorem_1_1 (k : ℕ) (hk : 0 < k) :
    (∃ n, ∃ G : SimpleGraph (Fin n), G.Connected ∧ c G = k) ↔
      k ∉ ({2, 4, 5, 8, 9, 16} : Finset ℕ) :=
  classification k hk

/-- **Theorem 1.1**, for graphs on an arbitrary finite vertex type. -/
theorem theorem_1_1_type (k : ℕ) (hk : 0 < k) :
    (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V), G.Connected ∧ c G = k) ↔
      k ∉ ({2, 4, 5, 8, 9, 16} : Finset ℕ) :=
  classification_type k hk

/-- **Theorem 1.2.** -/
theorem theorem_1_2 (k : ℕ) (hk : 0 < k) (hk' : k ∉ ({2, 4, 5, 8, 9, 16} : Finset ℕ)) :
    (∃ G : SimpleGraph (Fin (minOrder k)), G.Connected ∧ c G = k) ∧
      ∀ n (G : SimpleGraph (Fin n)), G.Connected → c G = k → minOrder k ≤ n :=
  least_order k hk hk'

theorem theorem_1_2_minOrder (k : ℕ) : minOrder k = if k = 25 then 6 else Nat.log 2 k + 1 := rfl

/-- **Theorem 1.3.** -/
theorem theorem_1_3 :
    (∀ m, 6 ≤ m → ∀ k, 2 ^ (m - 1) ≤ k → k < 2 ^ m → InV m k) ∧
      (∀ m, 7 ≤ m → ∀ k, m ≤ k → k < 2 ^ m → InLam m k) :=
  ⟨G_all, H_all⟩

/-- Theorem 1.3(a) fails for `m = 5`. -/
theorem theorem_1_3_sharp : ¬ InV 5 25 := fun h => by
  have := (V5_iff 25).1 h; omega

/-- The formulas of Section 1 for the path, the complete graph and the star. -/
theorem section_1_formulas (n d : ℕ) :
    c (pathGraph n) = T n ∧ c (⊤ : SimpleGraph (Fin n)) = 2 ^ n - 1 ∧
      c (coneG (⊥ : SimpleGraph (Fin d))) = 2 ^ d + d := by
  refine ⟨c_pathGraph n, ?_, c_star d⟩
  rw [c_top, Fintype.card_fin]

/-! ### Section 2 -/

section lemma_2_1
variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

/-- **Lemma 2.1(a)** (disjoint union). -/
theorem lemma_2_1_a (G : SimpleGraph V) (H : SimpleGraph W) : c (unionG G H) = c G + c H :=
  c_unionG G H

omit [DecidableEq V] in
/-- **Lemma 2.1(b)** (monotonicity, strict when an edge is added). -/
theorem lemma_2_1_b {H G : SimpleGraph V} (h : H ≤ G) :
    c H ≤ c G ∧ ∀ u v, G.Adj u v → ¬ H.Adj u v → c H < c G :=
  ⟨c_mono h, fun _ _ huv hnot => c_lt_of_adj h huv hnot⟩

/-- **Lemma 2.1(c)** (gluing at a vertex): `G[A]` and `G[B]` meet in `v` and no edge joins
`A \ {v}` and `B \ {v}`; `AS G A v` is `c_v(G[A])` and `NS G (A.erase v)` is `c(G[A] - v)`. -/
theorem lemma_2_1_c (G : SimpleGraph V) [DecidablePred (Sep G)] {A B : Finset V} {v : V}
    (hcov : A ∪ B = Finset.univ) (hAB : A ∩ B = {v})
    (hno : ∀ a ∈ A, ∀ b ∈ B, a ≠ v → b ≠ v → ¬ G.Adj a b) :
    c G = AS G A v * AS G B v + NS G (A.erase v) + NS G (B.erase v) :=
  c_glue hcov hAB hno

/-- **Lemma 2.1(d)** (cone). -/
theorem lemma_2_1_d (K : SimpleGraph V) : c (coneG K) = 2 ^ Fintype.card V + c K :=
  c_coneG K

/-- **Lemma 2.1(e)** (almost-cone), with `N` the neighbourhood of `u` in `K`, so `d = #N`. -/
theorem lemma_2_1_e (K : SimpleGraph V) (u : V) (N : Finset V) (hN : ∀ y, K.Adj u y ↔ y ∈ N) :
    c (aconeG K u) + 2 ^ (Fintype.card V - 1 - #N) = c K + 2 ^ Fintype.card V :=
  c_aconeG K u N hN

/-- **Lemma 2.1(f)** (range), with the extremal graphs. -/
theorem lemma_2_1_f (G : SimpleGraph V) (hG : G.Connected) :
    T (Fintype.card V) ≤ c G ∧ c G ≤ 2 ^ Fintype.card V - 1 :=
  ⟨T_le_c G hG, c_le G⟩

end lemma_2_1

/-! ### Section 3 -/

/-- **Lemma 3.1(a).** -/
theorem lemma_3_1_a (k : ℕ) :
    (InV 1 k ↔ k = 1) ∧ (InV 2 k ↔ k = 3) ∧ (InV 3 k ↔ k = 6 ∨ k = 7) ∧
      (InV 4 k ↔ 10 ≤ k ∧ k ≤ 15) :=
  ⟨V1_iff k, V2_iff k, V3_iff k, V4_iff k⟩

/-- **Lemma 3.1(b).** -/
theorem lemma_3_1_b (k : ℕ) :
    (InLam 2 k ↔ k = 2 ∨ k = 3) ∧ (InLam 3 k ↔ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 7) ∧
      (InLam 4 k ↔ (4 ≤ k ∧ k ≤ 8) ∨ (10 ≤ k ∧ k ≤ 15)) :=
  ⟨Lam2_iff k, Lam3_iff k, Lam4_iff k⟩

/-- **Proposition 3.2** (the gap above the path), with the equality case and the
characterization of the path. -/
theorem proposition_3_2 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) :
    (IsEmpty (pathGraph (Fintype.card V) ≃g G) →
      T (Fintype.card V) + (Fintype.card V - 3) ≤ c G) ∧
    (c G = T (Fintype.card V) ↔ Nonempty (pathGraph (Fintype.card V) ≃g G)) :=
  ⟨path_gap G hG, c_eq_T_iff G hG⟩

/-- **Proposition 3.2**, equality: the spider with legs `1, 1, n - 3`. -/
theorem proposition_3_2_spider (n : ℕ) (hn : 4 ≤ n) :
    (spiderG n).Connected ∧ c (spiderG n) = T n + (n - 3) :=
  ⟨spiderG_connected hn, c_spiderG hn⟩

/-- **Corollary 3.3.** -/
theorem corollary_3_3 :
    (∀ n k, T n < k → k < T n + (n - 3) → ¬ InV n k) ∧
      ∀ n (G : SimpleGraph (Fin n)), G.Connected → c G ≠ 16 := by
  refine ⟨gap_not_mem, fun n G hG h => ?_⟩
  have := exclusions G hG
  rw [h] at this
  simp at this

/-- **Proposition 3.4.** -/
theorem proposition_3_4 (k : ℕ) : InV 5 k ↔ k = 15 ∨ (17 ≤ k ∧ k ≤ 24) ∨ (26 ≤ k ∧ k ≤ 31) :=
  V5_iff k

/-- **Corollary 3.5.** -/
theorem corollary_3_5 (k : ℕ) (hk : 0 < k) (h16 : k ≤ 16) :
    (∃ n, ∃ G : SimpleGraph (Fin n), G.Connected ∧ c G = k) ↔
      k = 1 ∨ k = 3 ∨ k = 6 ∨ k = 7 ∨ (10 ≤ k ∧ k ≤ 15) :=
  values_le_16 k hk h16

/-! ### Section 4 -/

/-- **Lemma 4.2**: the rules (U), (C), (N), and the near-cone formula
`c(N(d,R)) + 2^r = 2^d + d + c(R) + 2^(d+1+r)`. -/
theorem lemma_4_2 :
    (∀ {a b m x y v : ℕ}, InV a x → InLam b y → a + b = m → x + y = v → InLam m v) ∧
    (∀ {k m x v : ℕ}, InLam k x → k + 1 = m → 2 ^ k + x = v → InV m v) ∧
    (∀ {d r m x v : ℕ}, InLam r x → 1 ≤ d → d + r + 2 = m →
      v + 2 ^ r = 2 ^ (d + r + 1) + 2 ^ d + d + x → InV m v) ∧
    (∀ (d : ℕ) {r : ℕ} (R : SimpleGraph (Fin r)),
      c (nearCone d R) + 2 ^ r = 2 ^ d + d + c R + 2 ^ (d + 1 + r)) :=
  ⟨fun hx hy hm hv => ruleU hx hy hm hv, fun hx hm hv => ruleC hx hm hv,
    fun hx hd hm hv => ruleN hx hd hm hv, fun d _ R => c_nearCone d R⟩

/-- **Lemma 4.3** (the sporadic graphs). -/
theorem lemma_4_3 : InV 5 19 ∧ InV 6 25 ∧ InV 6 32 ∧ InV 6 35 ∧ InV 6 57 ∧ InV 7 67 ∧ InV 7 90 :=
  ⟨sporadic_19, sporadic_25, sporadic_32, sporadic_35, sporadic_57, sporadic_67, sporadic_90⟩

/-- **Lemma 4.4(a).** -/
theorem lemma_4_4_a :
    (∀ k, (5 ≤ k ∧ k ≤ 24) ∨ (26 ≤ k ∧ k ≤ 31) → InLam 5 k) ∧
    (∀ k, (6 ≤ k ∧ k ≤ 25) ∨ (27 ≤ k ∧ k ≤ 63) → InLam 6 k) ∧
    (∀ k, 7 ≤ k → k ≤ 127 → InLam 7 k) := by
  refine ⟨?_, ?_, H7⟩
  · rintro k (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · interval_cases k
      exacts [L_5_5, L_5_6, L_5_7, L_5_8, L_5_9, L_5_10, L_5_11, L_5_12, L_5_13, L_5_14, L_5_15, L_5_16, L_5_17, L_5_18, L_5_19, L_5_20, L_5_21, L_5_22, L_5_23, L_5_24]
    · interval_cases k
      exacts [L_5_26, L_5_27, L_5_28, L_5_29, L_5_30, L_5_31]
  · rintro k (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · interval_cases k
      exacts [L_6_6, L_6_7, L_6_8, L_6_9, L_6_10, L_6_11, L_6_12, L_6_13, L_6_14, L_6_15, L_6_16, L_6_17, L_6_18, L_6_19, L_6_20, L_6_21, L_6_22, L_6_23, L_6_24, L_6_25]
    · interval_cases k
      exacts [L_6_27, L_6_28, L_6_29, L_6_30, L_6_31, L_6_32, L_6_33, L_6_34, L_6_35, L_6_36, L_6_37, L_6_38, L_6_39, L_6_40, L_6_41, L_6_42, L_6_43, L_6_44, L_6_45, L_6_46, L_6_47, L_6_48, L_6_49, L_6_50, L_6_51, L_6_52, L_6_53, L_6_54, L_6_55, L_6_56, L_6_57, L_6_58, L_6_59, L_6_60, L_6_61, L_6_62, L_6_63]

/-- **Lemma 4.4(b).** -/
theorem lemma_4_4_b :
    (∀ k, 17 ≤ k → k ≤ 31 → k ≠ 25 → InV 5 k) ∧ (∀ k, 32 ≤ k → k ≤ 63 → InV 6 k) ∧
      (∀ k, 64 ≤ k → k ≤ 127 → InV 7 k) :=
  ⟨V5I, G6, G7⟩

/-- **Remark 4.5**: `25 ∉ Λ_5`. -/
theorem remark_4_5 : ¬ InLam 5 25 := Lam5_ne_25

/-- **Theorem 4.6.** -/
theorem theorem_4_6 (m : ℕ) (hm : 8 ≤ m) :
    (∀ k, 2 ^ (m - 1) ≤ k → k < 2 ^ m → InV m k) ∧ (∀ k, m ≤ k → k < 2 ^ m → InLam m k) :=
  ⟨G_all m (by omega), H_all m (by omega)⟩

/-- **Example 4.7.** -/
theorem example_4_7 :
    (nearCone 2 (pathGraph 4)).Connected ∧ Fintype.card (Option (Option (Fin 2) ⊕ Fin 4)) = 8 ∧
      c (nearCone 2 (pathGraph 4)) = 128 :=
  c_nearCone_two_path

/-! ### Section 6 -/

/-- **Proposition 6.1.** -/
theorem proposition_6_1 (n : ℕ) (hn : 6 ≤ n) :
    InV n (T n) ∧ InV n (T n + (n - 3)) ∧ (∀ k, T n < k → k < T n + (n - 3) → ¬ InV n k) ∧
      (∀ k, 2 ^ (n - 1) ≤ k → k < 2 ^ n → InV n k) :=
  fixed_order n hn

/-! ### Section 7 -/

section lemma_7_2
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Lemma 7.2(a).** -/
theorem lemma_7_2_a (G : SimpleGraph V) [DecidableRel G.Adj] :
    F G = Fintype.card V + c G.lineGraph :=
  F_eq G

/-- **Lemma 7.2(b).** -/
theorem lemma_7_2_b (G : SimpleGraph V) : c G ≤ F G ∧ (c G = F G ↔ G.IsAcyclic) :=
  ⟨c_le_F G, c_eq_F_iff G⟩

/-- **Lemma 7.2(c).** -/
theorem lemma_7_2_c {H G : SimpleGraph V} (h : H ≤ G) {u v : V} (huv : G.Adj u v)
    (hnot : ¬ H.Adj u v) : F H < F G :=
  F_lt_of_adj h huv hnot

end lemma_7_2

end ConnectedSets.Paper
