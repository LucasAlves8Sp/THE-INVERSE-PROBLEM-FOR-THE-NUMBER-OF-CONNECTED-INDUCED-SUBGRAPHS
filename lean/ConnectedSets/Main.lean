/-
ConnectedSets/Main.lean

The graph classification of the paper (Theorems 1.1 and 1.2):

* `classification` : a positive integer `k` is the number of connected sets of some finite
  connected graph if and only if `k ∉ {2, 4, 5, 8, 9, 16}`;
* `classification_type` : the same statement for graphs on arbitrary finite types;
* `realize_minOrder`, `minOrder_le` : for `k ≥ 17` the least number of vertices of a connected
  graph with `c = k` is `⌊log₂ k⌋ + 1`, except for `k = 25`, where it is `6`.
-/
import ConnectedSets.Induction
import ConnectedSets.Five

open Finset

namespace ConnectedSets

/-! ### Exclusions -/

theorem T_mono : ∀ n, 6 ≤ n → 21 ≤ T n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih => rw [T_succ]; omega

/-- No connected graph has `c ∈ {2, 4, 5, 8, 9, 16}`. -/
theorem exclusions {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    c G ∉ ({2, 4, 5, 8, 9, 16} : Finset ℕ) := by
  have hup := c_le G
  have hlow := T_le_c G hG
  rw [Fintype.card_fin] at hup hlow
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  rcases (show n ≤ 5 ∨ 6 ≤ n by omega) with hn | hn
  · interval_cases n
    · norm_num at hup; omega
    · norm_num [T] at hup hlow; omega
    · norm_num [T] at hup hlow; omega
    · norm_num [T] at hup hlow; omega
    · norm_num [T] at hup hlow; omega
    · have h5 := (c_ne_of_five G hG).1
      norm_num [T] at hup hlow; omega
  · have := T_mono n hn
    omega

/-! ### Realization for every k ≥ 17, with the least order -/

/-- The least number of vertices of a connected graph with `c = k`, for `k ≥ 17`. -/
noncomputable def minOrder (k : ℕ) : ℕ := if k = 25 then 6 else Nat.log 2 k + 1

theorem realize_minOrder (k : ℕ) (hk : 17 ≤ k) : InV (minOrder k) k := by
  unfold minOrder
  split_ifs with h25
  · subst h25; exact sporadic_25
  · have hk0 : k ≠ 0 := by omega
    have h1 : 2 ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 hk0
    have h2 : k < 2 ^ (Nat.log 2 k + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
    have hlog : 4 ≤ Nat.log 2 k := by
      by_contra hlt
      push Not at hlt
      have : 2 ^ (Nat.log 2 k + 1) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at this
      omega
    rcases (show Nat.log 2 k = 4 ∨ 5 ≤ Nat.log 2 k by omega) with h4 | h5
    · rw [h4] at h2 ⊢
      norm_num at h2
      exact V5I k hk (by omega) h25
    · exact G_all (Nat.log 2 k + 1) (by omega) k (by simpa using h1) h2

theorem minOrder_le (k : ℕ) (hk : 17 ≤ k) {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected)
    (hc : c G = k) : minOrder k ≤ n := by
  have hup := c_le G
  rw [Fintype.card_fin, hc] at hup
  have hlt : k < 2 ^ n := by
    have : 0 < 2 ^ n := Nat.two_pow_pos n
    omega
  unfold minOrder
  split_ifs with h25
  · subst h25
    have h5 : 5 ≤ n := by
      by_contra hlt5
      push Not at hlt5
      have : 2 ^ n ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at this
      omega
    rcases (show n = 5 ∨ 6 ≤ n by omega) with rfl | h6
    · exact absurd hc (c_ne_of_five G hG).2
    · exact h6
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hlt
    omega

/-! ### The classification -/

/-- Values below 17. -/
theorem realize_small (k : ℕ) (hk : 0 < k) (hk16 : k ≤ 16)
    (hk' : k ∉ ({2, 4, 5, 8, 9, 16} : Finset ℕ)) : ∃ n, InV n k := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
  interval_cases k
  · exact ⟨1, V_1_1⟩
  · omega
  · exact ⟨2, V_2_3⟩
  · omega
  · omega
  · exact ⟨3, V_3_6⟩
  · exact ⟨3, V_3_7⟩
  · omega
  · omega
  · exact ⟨4, V_4_10⟩
  · exact ⟨4, V_4_11⟩
  · exact ⟨4, V_4_12⟩
  · exact ⟨4, V_4_13⟩
  · exact ⟨4, V_4_14⟩
  · exact ⟨4, V_4_15⟩
  · omega

/-- **Classification.** A positive integer `k` is the number of connected sets (vertex sets
inducing a connected subgraph) of some finite connected graph if and only if
`k ∉ {2, 4, 5, 8, 9, 16}`. -/
theorem classification (k : ℕ) (hk : 0 < k) :
    (∃ n, ∃ G : SimpleGraph (Fin n), G.Connected ∧ c G = k) ↔
      k ∉ ({2, 4, 5, 8, 9, 16} : Finset ℕ) := by
  constructor
  · rintro ⟨n, G, hG, rfl⟩
    exact exclusions G hG
  · intro hk'
    rcases (show k ≤ 16 ∨ 17 ≤ k by omega) with h | h
    · exact realize_small k hk h hk'
    · exact ⟨minOrder k, realize_minOrder k h⟩

/-- The classification for graphs on arbitrary finite types. -/
theorem classification_type (k : ℕ) (hk : 0 < k) :
    (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V), G.Connected ∧ c G = k) ↔
      k ∉ ({2, 4, 5, 8, 9, 16} : Finset ℕ) := by
  rw [← classification k hk]
  constructor
  · rintro ⟨V, _, _, G, hG, rfl⟩
    exact ⟨Fintype.card V, inV_of G hG rfl⟩
  · rintro ⟨n, G, hG, hc⟩
    exact ⟨Fin n, inferInstance, inferInstance, G, hG, hc⟩

/-- **Optimal order** (Theorem 1.2): for `k ≥ 17`, a connected graph with `c = k` exists on
`minOrder k` vertices, and every connected graph with `c = k` has at least that many. -/
theorem optimal_order (k : ℕ) (hk : 17 ≤ k) :
    (∃ G : SimpleGraph (Fin (minOrder k)), G.Connected ∧ c G = k) ∧
      ∀ n (G : SimpleGraph (Fin n)), G.Connected → c G = k → minOrder k ≤ n :=
  ⟨realize_minOrder k hk, fun _ G hG hc => minOrder_le k hk G hG hc⟩

theorem minOrder_eq (k : ℕ) (hk : k ≠ 25) : minOrder k = Nat.log 2 k + 1 := by
  simp [minOrder, hk]

end ConnectedSets
