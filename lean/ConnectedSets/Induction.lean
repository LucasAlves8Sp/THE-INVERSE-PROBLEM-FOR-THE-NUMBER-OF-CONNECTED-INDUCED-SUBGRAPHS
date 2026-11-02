/-
ConnectedSets/Induction.lean

Theorem 4.6 of the paper: for every m ≥ 8,
  (G_m)  every v ∈ [2^(m-1), 2^m - 1] is c of a connected graph on m vertices;
  (H_m)  every v ∈ [m, 2^m - 1] is c of a graph on m vertices.
The arithmetic is kept additive (x + 2^d + d = 2^r + j) to avoid truncated subtraction.
-/
import ConnectedSets.Intervals

namespace ConnectedSets

/-- (H_m). -/
def Hprop (m : ℕ) : Prop := ∀ v, m ≤ v → v < 2 ^ m → InLam m v

/-- (G_m). -/
def Gprop (m : ℕ) : Prop := ∀ v, 2 ^ (m - 1) ≤ v → v < 2 ^ m → InV m v

theorem H_seven : Hprop 7 := fun v h1 h2 => H7 v h1 (by norm_num at h2; omega)

theorem G_six : Gprop 6 := fun v h1 h2 => G6 v (by norm_num at h1; omega) (by norm_num at h2; omega)

theorem G_seven : Gprop 7 := fun v h1 h2 => G7 v (by norm_num at h1; omega) (by norm_num at h2; omega)

/-- `e + 3 ≤ 2^e` for `e ≥ 3`. -/
theorem add_three_le_two_pow : ∀ e, 3 ≤ e → e + 3 ≤ 2 ^ e := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih => rw [pow_succ]; omega

/-- `2e + 1 ≤ 2^e` for `e ≥ 3`. -/
theorem two_mul_add_one_le_two_pow : ∀ e, 3 ≤ e → 2 * e + 1 ≤ 2 ^ e := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih => rw [pow_succ]; omega

theorem G_of_H (m : ℕ) (hm : 8 ≤ m) (IH : ∀ k, 7 ≤ k → k < m → Hprop k) : Gprop m := by
  intro v hv1 hv2
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hv1
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  rw [hpow] at hv2
  by_cases hbig : 2 ^ k + k ≤ v
  · -- cone over a graph on k vertices with c = v - 2^k
    exact ruleC (k := k) (x := v - 2 ^ k)
      (IH k (by omega) (by omega) (v - 2 ^ k) (by omega) (by omega)) rfl (by omega)
  · -- near-cone; j = v - 2^k < k
    obtain ⟨j, rfl⟩ : ∃ j, v = 2 ^ k + j := ⟨v - 2 ^ k, by omega⟩
    have hjk : j < k := by omega
    rcases (show k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ 11 ≤ k by omega) with h | h | h | h | h
    · -- m = 8
      subst h
      rcases (show j ≤ 5 ∨ j = 6 by omega) with hj | hj
      · exact ruleN (d := 2) (r := 4) (x := 10 + j) (L4I (10 + j) (by omega) (by omega))
          (by norm_num) (by norm_num) (by norm_num; omega)
      · subst hj
        exact ruleN (d := 3) (r := 3) (x := 3) L_3_3 (by norm_num) (by norm_num) (by norm_num)
    · -- m = 9
      subst h
      rcases (show j ≤ 5 ∨ 6 ≤ j by omega) with hj | hj
      · exact ruleN (d := 2) (r := 5) (x := 26 + j) (L5I (26 + j) (by omega) (by omega) (by omega))
          (by norm_num) (by norm_num) (by norm_num; omega)
      · rcases (show j = 6 ∨ j = 7 by omega) with rfl | rfl
        · exact ruleN (d := 3) (r := 4) (x := 11) L_4_11 (by norm_num) (by norm_num) (by norm_num)
        · exact ruleN (d := 3) (r := 4) (x := 12) L_4_12 (by norm_num) (by norm_num) (by norm_num)
    · -- m = 10
      subst h
      by_cases hj : j = 4
      · subst hj
        exact ruleN (d := 2) (r := 6) (x := 62) L_6_62 (by norm_num) (by norm_num) (by norm_num)
      · exact ruleN (d := 3) (r := 5) (x := 21 + j) (L5I (21 + j) (by omega) (by omega) (by omega))
          (by norm_num) (by norm_num) (by norm_num; omega)
    · -- m = 11
      subst h
      exact ruleN (d := 3) (r := 6) (x := 53 + j) (L6I (53 + j) (by omega) (by omega))
        (by norm_num) (by norm_num) (by norm_num; omega)
    · -- m ≥ 12: the general choice of d
      classical
      have hex : ∃ d, k ≤ 2 ^ d + d := ⟨k, by have := Nat.lt_two_pow_self (n := k); omega⟩
      set d := Nat.find hex with hddef
      have hd : k ≤ 2 ^ d + d := Nat.find_spec hex
      have hdmin : ∀ d' < d, 2 ^ d' + d' < k := by
        intro d' h'
        have := Nat.find_min hex h'
        omega
      have hd3 : 3 ≤ d := by
        by_contra hlt
        push Not at hlt
        have : 2 ^ d ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num at this
        omega
      have hdk : d + 1 ≤ k := by
        by_contra hlt
        push Not at hlt
        have h1 := hdmin (d - 1) (by omega)
        have h2 : 1 ≤ 2 ^ (d - 1) := Nat.one_le_two_pow
        omega
      obtain ⟨r, hrdef⟩ : ∃ r, r = k - 1 - d := ⟨_, rfl⟩
      have hr : 7 ≤ r ∧ d + 1 ≤ r := by
        rcases (show d = 3 ∨ 4 ≤ d by omega) with h3 | h4
        · have : k ≤ 11 := by rw [h3] at hd; norm_num at hd; omega
          omega
        · have hmin := hdmin (d - 1) (by omega)
          have hp := add_three_le_two_pow (d - 1) (by omega)
          have h8 : 2 ^ 3 ≤ 2 ^ (d - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
          norm_num at h8
          omega
      obtain ⟨hr7, hdr⟩ := hr
      -- powers: 2^d + d + r ≤ 2^r
      obtain ⟨e, rfl⟩ : ∃ e, r = e + 1 := ⟨r - 1, by omega⟩
      have hde : 2 ^ d ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      have he : 2 * e + 1 ≤ 2 ^ e := two_mul_add_one_le_two_pow e (by omega)
      have hre : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
      have hbound : 2 ^ d + d + (e + 1) ≤ 2 ^ (e + 1) := by omega
      obtain ⟨x, hx⟩ : ∃ x, x + (2 ^ d + d) = 2 ^ (e + 1) + j := ⟨2 ^ (e + 1) + j - (2 ^ d + d), by omega⟩
      have hx1 : e + 1 ≤ x := by omega
      have hx2 : x < 2 ^ (e + 1) := by omega
      have hxL : InLam (e + 1) x := IH (e + 1) (by omega) (by omega) x hx1 hx2
      have hk : d + (e + 1) + 1 = k := by omega
      refine ruleN (d := d) (r := e + 1) (x := x) hxL (by omega) (by omega) ?_
      rw [hk]
      omega

theorem H_of_G (m : ℕ) (hm : 8 ≤ m) (hG : Gprop m) (hH : Hprop (m - 1)) : Hprop m := by
  intro v hv1 hv2
  by_cases hlow : v < 2 ^ (m - 1)
  · exact ruleU (a := 1) (b := m - 1) (x := 1) (y := v - 1) V_1_1
      (hH (v - 1) (by omega) (by omega)) (by omega) (by omega)
  · exact (hG v (by omega) hv2).inLam

theorem H_all : ∀ m, 7 ≤ m → Hprop m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases (show m = 7 ∨ 8 ≤ m by omega) with rfl | h8
    · exact H_seven
    · have IH : ∀ k, 7 ≤ k → k < m → Hprop k := fun k hk1 hk2 => ih k hk2 hk1
      exact H_of_G m h8 (G_of_H m h8 IH) (IH (m - 1) (by omega) (by omega))

/-- Theorem 4.6 together with Lemma 4.4: (G_m) for every m ≥ 6. -/
theorem G_all : ∀ m, 6 ≤ m → Gprop m := by
  intro m hm
  rcases (show m = 6 ∨ m = 7 ∨ 8 ≤ m by omega) with rfl | rfl | h8
  · exact G_six
  · exact G_seven
  · exact G_of_H m h8 (fun k hk1 _ => H_all k hk1)

end ConnectedSets
