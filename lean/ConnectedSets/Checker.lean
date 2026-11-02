/-
ConnectedSets/Checker.lean

A kernel-evaluable count of connected sets on bitmasks, proved equal to `c`.

Vertex sets of `Fin n` are encoded by natural numbers `m < 2^n` (bit `i` set iff `i ∈ S`);
a graph is given by neighbourhood masks `a i`. A set `S` is tested for connectivity by
growing the closure of its least vertex `n` times.
-/
import ConnectedSets.Transport

open Finset

namespace ConnectedSets

/-! ### Bitmasks and vertex sets -/

/-- The vertex set encoded by a bitmask. -/
def ofMask {n : ℕ} (m : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => m.testBit i = true)

@[simp] theorem mem_ofMask {n m : ℕ} {i : Fin n} :
    i ∈ (ofMask m : Finset (Fin n)) ↔ m.testBit i = true := by
  simp [ofMask]

theorem testBit_eq_false_of_lt_two_pow {x n j : ℕ} (hx : x < 2 ^ n) (hj : n ≤ j) :
    x.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) hj))

theorem ofMask_injOn {n : ℕ} :
    Set.InjOn (fun m => (ofMask m : Finset (Fin n))) (Finset.range (2 ^ n) : Set ℕ) := by
  intro m hm m' hm' h
  simp only [Finset.coe_range, Set.mem_Iio] at hm hm'
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < n
  · have := congrArg (fun S : Finset (Fin n) => (⟨j, hj⟩ : Fin n) ∈ S) h
    simp only [mem_ofMask] at this
    cases h1 : m.testBit j <;> cases h2 : m'.testBit j <;> simp_all
  · push Not at hj
    rw [testBit_eq_false_of_lt_two_pow hm hj, testBit_eq_false_of_lt_two_pow hm' hj]

theorem image_ofMask_range (n : ℕ) :
    (Finset.range (2 ^ n)).image (fun m => (ofMask m : Finset (Fin n))) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_image_of_injOn ofMask_injOn, Finset.card_range, Fintype.card_finset,
    Fintype.card_fin]

/-! ### Neighbourhoods, one closure step, closure -/

/-- `nbrM a k R` is the union of the masks `a i` over the bits `i < k` of `R`. -/
def nbrM (a : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, R => nbrM a k R ||| (if R.testBit k then a k else 0)

theorem testBit_nbrM (a : ℕ → ℕ) (k R j : ℕ) :
    (nbrM a k R).testBit j = true ↔ ∃ i < k, R.testBit i = true ∧ (a i).testBit j = true := by
  induction k with
  | zero => simp [nbrM]
  | succ k ih =>
    simp only [nbrM, Nat.testBit_or, Bool.or_eq_true, ih]
    constructor
    · rintro (⟨i, hi, h⟩ | h)
      · exact ⟨i, by omega, h⟩
      · by_cases hk : R.testBit k = true
        · simp only [hk, ↓reduceIte] at h; exact ⟨k, by omega, hk, h⟩
        · simp [hk] at h
    · rintro ⟨i, hi, hRi, hai⟩
      by_cases hik : i < k
      · exact Or.inl ⟨i, hik, hRi, hai⟩
      · have : i = k := by omega
        subst this
        right; simp only [hRi, ↓reduceIte]; exact hai

/-- One closure step inside `S`. -/
def stepM (a : ℕ → ℕ) (n S R : ℕ) : ℕ := R ||| (nbrM a n R &&& S)

open Classical in
/-- The Finset version of a closure step. -/
noncomputable def stepF {n : ℕ} (G : SimpleGraph (Fin n)) (S R : Finset (Fin n)) : Finset (Fin n) :=
  R ∪ ((Finset.univ.filter (fun j => ∃ i ∈ R, G.Adj i j)) ∩ S)

theorem ofMask_stepM {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ → ℕ)
    (ha : ∀ i j : Fin n, (a i).testBit j = true ↔ G.Adj i j) (S R : ℕ) :
    (ofMask (stepM a n S R) : Finset (Fin n)) = stepF G (ofMask S) (ofMask R) := by
  classical
  ext j
  simp only [stepM, mem_ofMask, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true,
    Bool.and_eq_true, testBit_nbrM, stepF, Finset.mem_union, Finset.mem_inter,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨⟨i, hi, hRi, hai⟩, hS⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨⟨i, hi⟩, hRi, (ha ⟨i, hi⟩ j).1 hai⟩, hS⟩
  · rintro (h | ⟨⟨i, hRi, hadj⟩, hS⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨i, i.2, hRi, (ha i j).2 hadj⟩, hS⟩

theorem ofMask_iterate {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ → ℕ)
    (ha : ∀ i j : Fin n, (a i).testBit j = true ↔ G.Adj i j) (S : ℕ) :
    ∀ f R, (ofMask ((stepM a n S)^[f] R) : Finset (Fin n)) = (stepF G (ofMask S))^[f] (ofMask R) := by
  intro f
  induction f with
  | zero => intro R; rfl
  | succ f ih =>
    intro R
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, ofMask_stepM G a ha]

/-- The bits of the closure stay inside `S`. -/
theorem iterate_bits_sub (a : ℕ → ℕ) (n S : ℕ) :
    ∀ f R, (∀ j, R.testBit j = true → S.testBit j = true) →
      ∀ j, ((stepM a n S)^[f] R).testBit j = true → S.testBit j = true := by
  intro f
  induction f with
  | zero => intro R hR; exact hR
  | succ f ih =>
    intro R hR
    rw [Function.iterate_succ_apply]
    apply ih
    intro j hj
    simp only [stepM, Nat.testBit_or, Nat.testBit_and, Bool.or_eq_true, Bool.and_eq_true] at hj
    rcases hj with h | ⟨-, h⟩
    · exact hR j h
    · exact h

/-! ### Closure and connectivity on Finsets -/

theorem stepF_sub {n : ℕ} (G : SimpleGraph (Fin n)) {S R : Finset (Fin n)} (hR : R ⊆ S) :
    stepF G S R ⊆ S := by
  intro x hx
  rcases Finset.mem_union.1 hx with h | h
  · exact hR h
  · exact (Finset.mem_inter.1 h).2

theorem le_stepF {n : ℕ} (G : SimpleGraph (Fin n)) (S R : Finset (Fin n)) : R ⊆ stepF G S R :=
  Finset.subset_union_left

theorem iterate_stepF_sub {n : ℕ} (G : SimpleGraph (Fin n)) {S R : Finset (Fin n)} (hR : R ⊆ S) :
    ∀ k, (stepF G S)^[k] R ⊆ S := by
  intro k
  induction k with
  | zero => exact hR
  | succ k ih => rw [Function.iterate_succ_apply']; exact stepF_sub G ih

theorem iterate_stepF_mono {n : ℕ} (G : SimpleGraph (Fin n)) (S R : Finset (Fin n)) :
    ∀ k, R ⊆ (stepF G S)^[k] R := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih => rw [Function.iterate_succ_apply']; exact ih.trans (le_stepF G S _)

/-- If the closure of a vertex of `S` is `S`, then `S` is connected. -/
theorem sep_of_iterate_eq {n : ℕ} (G : SimpleGraph (Fin n)) {S : Finset (Fin n)} {r : Fin n}
    (hr : r ∈ S) {f : ℕ} (hf : (stepF G S)^[f] {r} = S) : Sep G S := by
  classical
  refine ⟨⟨r, hr⟩, ?_⟩
  intro A hAS hAne hAneS
  by_contra hno
  push Not at hno
  -- hno : ∀ a ∈ A, ∀ b ∈ S, b ∉ A → ¬ G.Adj a b
  by_cases hrA : r ∈ A
  · have hsub : ∀ k, (stepF G S)^[k] {r} ⊆ A := by
      intro k
      induction k with
      | zero => simpa using hrA
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        intro x hx
        rcases Finset.mem_union.1 hx with h | h
        · exact ih h
        · simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at h
          obtain ⟨⟨i, hi, hix⟩, hxS⟩ := h
          by_contra hxA
          exact hno i (ih hi) x hxS hxA hix
    exact hAneS (Finset.Subset.antisymm hAS (hf ▸ hsub f))
  · have hsub : ∀ k, (stepF G S)^[k] {r} ⊆ S \ A := by
      intro k
      induction k with
      | zero => simp [hr, hrA]
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        intro x hx
        rcases Finset.mem_union.1 hx with h | h
        · exact ih h
        · simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at h
          obtain ⟨⟨i, hi, hix⟩, hxS⟩ := h
          have hiS := Finset.mem_sdiff.1 (ih hi)
          refine Finset.mem_sdiff.2 ⟨hxS, ?_⟩
          intro hxA
          exact hno x hxA i hiS.1 hiS.2 hix.symm
    obtain ⟨y, hyA⟩ := hAne
    have : y ∈ S \ A := (hf ▸ hsub f) (hAS hyA)
    exact (Finset.mem_sdiff.1 this).2 hyA

/-- If `S` is connected, the closure of any of its vertices reaches `S` within `#S - 1` steps. -/
theorem iterate_eq_of_sep {n : ℕ} (G : SimpleGraph (Fin n)) {S : Finset (Fin n)} (hS : Sep G S)
    {r : Fin n} (hr : r ∈ S) {f : ℕ} (hf : #S ≤ f + 1) : (stepF G S)^[f] {r} = S := by
  classical
  have hR0 : ({r} : Finset (Fin n)) ⊆ S := by simpa using hr
  have key : ∀ k, (stepF G S)^[k] {r} = S ∨ k + 1 ≤ #((stepF G S)^[k] {r}) := by
    intro k
    induction k with
    | zero => right; simp
    | succ k ih =>
      rcases ih with h | h
      · left
        rw [Function.iterate_succ_apply', h]
        exact Finset.Subset.antisymm (stepF_sub G le_rfl) (le_stepF G S S)
      · by_cases heq : (stepF G S)^[k] {r} = S
        · left
          rw [Function.iterate_succ_apply', heq]
          exact Finset.Subset.antisymm (stepF_sub G le_rfl) (le_stepF G S S)
        · right
          set R := (stepF G S)^[k] {r} with hRdef
          have hRS : R ⊆ S := iterate_stepF_sub G hR0 k
          have hrR : r ∈ R := iterate_stepF_mono G S {r} k (Finset.mem_singleton_self r)
          obtain ⟨a, haR, b, hbS, hbR, hab⟩ := hS.2 R hRS ⟨r, hrR⟩ heq
          have hb : b ∈ stepF G S R := by
            refine Finset.mem_union.2 (Or.inr ?_)
            simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨⟨a, haR, hab⟩, hbS⟩
          have hlt : R ⊂ stepF G S R :=
            Finset.ssubset_iff_subset_ne.2 ⟨le_stepF G S R, fun h => hbR (h ▸ hb)⟩
          have hlt' := Finset.card_lt_card hlt
          rw [Function.iterate_succ_apply']
          change k + 1 + 1 ≤ #(stepF G S R)
          omega
  rcases key f with h | h
  · exact h
  · by_contra heq
    have hsub := iterate_stepF_sub G hR0 f
    have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, heq⟩)
    omega

/-! ### The checker -/

/-- Connectivity of the set encoded by `S`, for the graph with neighbourhood masks `a`. -/
def connM (a : ℕ → ℕ) (n S : ℕ) : Bool :=
  match (List.range n).find? (fun i => S.testBit i) with
  | none => false
  | some i => (stepM a n S)^[n] (2 ^ i) == S

/-- The number of connected sets of the graph with neighbourhood masks `a` on `n` vertices. -/
def cM (a : ℕ → ℕ) (n : ℕ) : ℕ := ((Finset.range (2 ^ n)).filter (fun m => connM a n m = true)).card

theorem connM_iff {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ → ℕ)
    (ha : ∀ i j : Fin n, (a i).testBit j = true ↔ G.Adj i j) {S : ℕ} (hS : S < 2 ^ n) :
    connM a n S = true ↔ Sep G (ofMask S) := by
  classical
  unfold connM
  cases hfind : (List.range n).find? (fun i => S.testBit i) with
  | none =>
    simp only [Bool.false_eq_true, false_iff]
    rintro ⟨⟨x, hx⟩, -⟩
    rw [mem_ofMask] at hx
    have := List.find?_eq_none.1 hfind x (List.mem_range.2 x.2)
    simp_all
  | some i =>
    have hi : i < n := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
    have hSi : S.testBit i = true := by simpa using List.find?_some hfind
    set r : Fin n := ⟨i, hi⟩
    have hr : r ∈ (ofMask S : Finset (Fin n)) := by simpa [r] using hSi
    have hR0 : (ofMask (2 ^ i) : Finset (Fin n)) = {r} := by
      ext j
      simp only [mem_ofMask, Nat.testBit_two_pow, decide_eq_true_eq, Finset.mem_singleton, r]
      constructor
      · intro h; ext; exact h.symm
      · intro h; rw [h]
    have hbits : ∀ j, (2 ^ i).testBit j = true → S.testBit j = true := by
      intro j hj
      rw [Nat.testBit_two_pow, decide_eq_true_eq] at hj
      subst hj; exact hSi
    have heqiff : ((stepM a n S)^[n] (2 ^ i) == S) = true ↔
        (stepF G (ofMask S))^[n] {r} = ofMask S := by
      rw [beq_iff_eq, ← hR0, ← ofMask_iterate G a ha S n (2 ^ i)]
      constructor
      · intro h; rw [h]
      · intro h
        apply Nat.eq_of_testBit_eq
        intro j
        by_cases hj : j < n
        · have := congrArg (fun T : Finset (Fin n) => (⟨j, hj⟩ : Fin n) ∈ T) h
          simp only [mem_ofMask] at this
          cases h1 : ((stepM a n S)^[n] (2 ^ i)).testBit j <;> cases h2 : S.testBit j <;> simp_all
        · push Not at hj
          rw [testBit_eq_false_of_lt_two_pow hS hj]
          cases h1 : ((stepM a n S)^[n] (2 ^ i)).testBit j
          · rfl
          · have := iterate_bits_sub a n S n (2 ^ i) hbits j h1
            rw [testBit_eq_false_of_lt_two_pow hS hj] at this
            exact absurd this (by simp)
    simp only
    rw [heqiff]
    constructor
    · exact sep_of_iterate_eq G hr
    · intro hsep
      apply iterate_eq_of_sep G hsep hr
      have := Finset.card_le_univ (ofMask S : Finset (Fin n))
      rw [Fintype.card_fin] at this
      omega

theorem c_eq_cM {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ → ℕ)
    (ha : ∀ i j : Fin n, (a i).testBit j = true ↔ G.Adj i j) : c G = cM a n := by
  classical
  rw [c_eq_card_sep]
  unfold cM
  rw [← Finset.card_image_of_injOn (f := fun m => (ofMask m : Finset (Fin n)))
    (ofMask_injOn.mono (by intro x hx; simp only [Finset.coe_filter] at hx; simpa using hx.1))]
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_range]
  constructor
  · intro hT
    have : T ∈ (Finset.range (2 ^ n)).image (fun m => (ofMask m : Finset (Fin n))) := by
      rw [image_ofMask_range]; exact Finset.mem_univ _
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 this
    rw [Finset.mem_range] at hm
    exact ⟨m, ⟨hm, (connM_iff G a ha hm).2 hT⟩, rfl⟩
  · rintro ⟨m, ⟨hm, hc⟩, rfl⟩
    exact (connM_iff G a ha hm).1 hc

theorem connected_iff_connM {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℕ → ℕ)
    (ha : ∀ i j : Fin n, (a i).testBit j = true ↔ G.Adj i j) :
    G.Connected ↔ connM a n (2 ^ n - 1) = true := by
  classical
  rw [connected_iff_sep_univ, connM_iff G a ha (Nat.sub_lt (Nat.two_pow_pos n) one_pos)]
  have : (ofMask (2 ^ n - 1) : Finset (Fin n)) = Finset.univ := by
    ext j; simp [Nat.testBit_two_pow_sub_one]
  rw [this]

/-! ### Graphs given by masks -/

/-- The graph on `Fin n` whose neighbourhood masks are (the symmetrization of) `a`. -/
def ofMasks {n : ℕ} (a : ℕ → ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ((a i).testBit j = true ∨ (a j).testBit i = true)
  symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, h2.symm⟩⟩
  loopless := ⟨fun _ ⟨h, _⟩ => h rfl⟩

theorem ofMasks_ha {n : ℕ} (a : ℕ → ℕ)
    (hsym : ∀ i j : Fin n, (a i).testBit j = (a j).testBit i)
    (hirr : ∀ i : Fin n, (a i).testBit i = false) :
    ∀ i j : Fin n, (a i).testBit j = true ↔ (ofMasks (n := n) a).Adj i j := by
  intro i j
  simp only [ofMasks]
  constructor
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl; rw [hirr] at h; exact absurd h (by simp)
  · rintro ⟨-, h | h⟩
    · exact h
    · rw [hsym]; exact h

/-- Certificate form: a concrete mask table with `connM` true and `cM = v` gives `v ∈ V_n`. -/
theorem inV_of_masks {n v : ℕ} (a : ℕ → ℕ)
    (hsym : ∀ i j : Fin n, (a i).testBit j = (a j).testBit i)
    (hirr : ∀ i : Fin n, (a i).testBit i = false)
    (hconn : connM a n (2 ^ n - 1) = true) (hc : cM a n = v) : InV n v := by
  have ha := ofMasks_ha a hsym hirr
  exact ⟨ofMasks a, (connected_iff_connM _ a ha).2 hconn, by rw [c_eq_cM _ a ha, hc]⟩

end ConnectedSets
