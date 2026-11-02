/-
ConnectedSets/Transport.lean

The sets of values
  `InLam m v` : some graph on `Fin m` has `c = v`        (v ∈ Λ_m in the paper)
  `InV m v`   : some connected graph on `Fin m` has `c = v` (v ∈ V_m)
and the rules (U), (C), (N) of Lemma 4.2 of the paper, together with the near-cone formula.
-/
import ConnectedSets.Rules

open Finset

namespace ConnectedSets

/-- `v ∈ Λ_m`: some graph with exactly `m` vertices has `c = v`. -/
def InLam (m v : ℕ) : Prop := ∃ G : SimpleGraph (Fin m), c G = v

/-- `v ∈ V_m`: some connected graph with exactly `m` vertices has `c = v`. -/
def InV (m v : ℕ) : Prop := ∃ G : SimpleGraph (Fin m), G.Connected ∧ c G = v

theorem InV.inLam {m v : ℕ} (h : InV m v) : InLam m v := by
  obtain ⟨G, -, hG⟩ := h; exact ⟨G, hG⟩

variable {V : Type*}

theorem inLam_of [Fintype V] [DecidableEq V] (G : SimpleGraph V) {m : ℕ}
    (h : Fintype.card V = m) : InLam m (c G) := by
  let e := Fintype.equivFinOfCardEq h
  exact ⟨G.map e, (c_congr (SimpleGraph.Iso.map e G)).symm⟩

theorem inV_of [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.Connected) {m : ℕ}
    (h : Fintype.card V = m) : InV m (c G) := by
  let e := Fintype.equivFinOfCardEq h
  exact ⟨G.map e, (SimpleGraph.Iso.map e G).connected_iff.1 hG,
    (c_congr (SimpleGraph.Iso.map e G)).symm⟩

/-- The empty graph: `0 ∈ Λ_0`. -/
theorem inLam_zero : InLam 0 0 := by
  refine ⟨⊥, ?_⟩
  rw [c_edgeless]; simp

/-- The one-vertex graph: `1 ∈ V_1`. -/
theorem inV_one : InV 1 1 := by
  refine ⟨⊥, ?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]
    exact ⟨0, fun w => by rw [Subsingleton.elim w 0]⟩
  · rw [c_edgeless]; simp

/-- Rule (U): `x ∈ V_a`, `y ∈ Λ_b` give `x + y ∈ Λ_(a+b)`. -/
theorem ruleU {a b m x y v : ℕ} (hx : InV a x) (hy : InLam b y) (hm : a + b = m) (hv : x + y = v) :
    InLam m v := by
  obtain ⟨G, -, rfl⟩ := hx
  obtain ⟨H, rfl⟩ := hy
  have := inLam_of (unionG G H) (m := m) (by simp [hm])
  rwa [c_unionG, hv] at this

/-- Rule (C): `x ∈ Λ_k` gives `2^k + x ∈ V_(k+1)`. -/
theorem ruleC {k m x v : ℕ} (hx : InLam k x) (hm : k + 1 = m) (hv : 2 ^ k + x = v) : InV m v := by
  obtain ⟨K, rfl⟩ := hx
  have := inV_of (coneG K) (coneG_connected K) (m := m) (by simp [hm])
  rwa [c_coneG, Fintype.card_fin, hv] at this

/-- The near-cone `N(d,R)`: almost-cone over `K_{1,d} ⊔ R`, missing the centre of the star. -/
def nearCone (d : ℕ) {r : ℕ} (R : SimpleGraph (Fin r)) :
    SimpleGraph (Option (Option (Fin d) ⊕ Fin r)) :=
  aconeG (unionG (coneG (⊥ : SimpleGraph (Fin d))) R) (Sum.inl none)

theorem c_nearCone (d : ℕ) {r : ℕ} (R : SimpleGraph (Fin r)) :
    c (nearCone d R) + 2 ^ r = 2 ^ d + d + c R + 2 ^ (d + 1 + r) := by
  classical
  set K := unionG (coneG (⊥ : SimpleGraph (Fin d))) R with hK
  set N : Finset (Option (Fin d) ⊕ Fin r) :=
    (Finset.univ : Finset (Fin d)).map (Function.Embedding.some.trans Function.Embedding.inl) with hNdef
  have hN : ∀ y, K.Adj (Sum.inl none) y ↔ y ∈ N := by
    rintro ((_ | i) | j)
    · simp [hK, hNdef, coneG]
    · simp [hK, hNdef, coneG]
    · simp [hK, hNdef]
  have hcardN : #N = d := by simp [hNdef]
  have hcardK : Fintype.card (Option (Fin d) ⊕ Fin r) = d + 1 + r := by simp
  have h := c_aconeG K (Sum.inl none) N hN
  rw [hcardN, hcardK] at h
  have h2 : d + 1 + r - 1 - d = r := by omega
  rw [h2] at h
  have hcK : c K = 2 ^ d + d + c R := by
    rw [hK, c_unionG, c_coneG, c_edgeless, Fintype.card_fin]
  unfold nearCone
  rw [← hK]
  omega

theorem nearCone_connected (d : ℕ) (hd : 1 ≤ d) {r : ℕ} (R : SimpleGraph (Fin r)) :
    (nearCone d R).Connected := by
  apply aconeG_connected _ _ (Sum.inl (some ⟨0, hd⟩))
  show (coneG (⊥ : SimpleGraph (Fin d))).Adj (some ⟨0, hd⟩) none
  exact trivial

/-- Rule (N): `x ∈ Λ_r`, `d ≥ 1`, `m = d + r + 2` give `v ∈ V_m` when
`v + 2^r = 2^(d+r+1) + 2^d + d + x`, i.e. `v = 2^(m-1) - 2^r + 2^d + d + x`. -/
theorem ruleN {d r m x v : ℕ} (hx : InLam r x) (hd : 1 ≤ d) (hm : d + r + 2 = m)
    (hv : v + 2 ^ r = 2 ^ (d + r + 1) + 2 ^ d + d + x) : InV m v := by
  obtain ⟨R, rfl⟩ := hx
  have hc := c_nearCone d R
  have hexp : d + 1 + r = d + r + 1 := by omega
  rw [hexp] at hc
  have hcv : c (nearCone d R) = v := by omega
  have h := inV_of (nearCone d R) (nearCone_connected d hd R) (m := m) (by simp; omega)
  rwa [hcv] at h

end ConnectedSets
