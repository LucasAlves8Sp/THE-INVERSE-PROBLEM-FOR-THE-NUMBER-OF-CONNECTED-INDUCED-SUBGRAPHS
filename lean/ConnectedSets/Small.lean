/-
ConnectedSets/Small.lean

Small orders and further statements of the paper:
* Lemma 2.1(b) (`c_mono`, `c_lt_of_adj`), Lemma 2.1(f) attained by `K_n` (`c_top`), and the
  bound `c G ≥ |V|` (`card_le_c`);
* Lemma 3.1 (`V1_iff` … `V4_iff`, `Lam2_iff`, `Lam3_iff`, `Lam4_iff`); the values `5 ∉ Λ_3` and
  `9 ∉ Λ_4` are checked in the kernel over all labeled graphs on three and four vertices;
* Corollary 3.3 (`gap_not_mem`), Proposition 3.4 (`V5_iff`), Corollary 3.5 (`values_le_16`);
* Theorem 1.2 for every attainable value (`least_order`);
* Proposition 6.1 (`fixed_order`).
-/
import ConnectedSets.Main
import ConnectedSets.Spider

open Finset SimpleGraph

namespace ConnectedSets

variable {V : Type*}

/-! ### Lemma 2.1(b), Lemma 2.1(f), and `c ≥ |V|` -/

theorem sep_mono {H G : SimpleGraph V} (h : H ≤ G) {S : Finset V} (hS : Sep H S) : Sep G S := by
  refine ⟨hS.1, fun A hA hAne hAS => ?_⟩
  obtain ⟨a, ha, b, hb, hbA, hab⟩ := hS.2 A hA hAne hAS
  exact ⟨a, ha, b, hb, hbA, h hab⟩

/-- **Lemma 2.1(b)**, first part: `c` is monotone under adding edges. -/
theorem c_mono [Fintype V] {H G : SimpleGraph V} (h : H ≤ G) : c H ≤ c G := by
  classical
  rw [c_eq_card_sep, c_eq_card_sep]
  apply Finset.card_le_card
  intro S hS
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  exact sep_mono h hS

theorem adj_of_sep_pair [DecidableEq V] {H : SimpleGraph V} {u v : V} (huv : u ≠ v)
    (h : Sep H {u, v}) : H.Adj u v := by
  obtain ⟨a, ha, b, hb, hbA, hab⟩ := h.2 {u} (by simp) (by simp) (by
    intro h'; have : v ∈ ({u} : Finset V) := by rw [h']; simp
    exact huv (Finset.mem_singleton.1 this).symm)
  rw [Finset.mem_singleton] at ha hbA
  subst ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb
  rcases hb with rfl | rfl
  · exact absurd rfl hbA
  · exact hab

/-- **Lemma 2.1(b)**, second part: adding a missing edge strictly increases `c`. -/
theorem c_lt_of_adj [Fintype V] {H G : SimpleGraph V} (h : H ≤ G) {u v : V} (huv : G.Adj u v)
    (hnot : ¬ H.Adj u v) : c H < c G := by
  classical
  rw [c_eq_card_sep, c_eq_card_sep]
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
    exact sep_mono h hS
  · intro hsub
    have hne : u ≠ v := G.ne_of_adj huv
    have hG : Sep G {u, v} := by
      have := sep_insert (sep_singleton G v) (b := u) (by simpa using hne) ⟨v, by simp, huv.symm⟩
      exact this
    have := hsub (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hG)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hnot (adj_of_sep_pair hne this)

/-- Every graph has at least `|V|` connected sets, its singletons. -/
theorem card_le_c [Fintype V] (G : SimpleGraph V) : Fintype.card V ≤ c G := by
  classical
  rw [c_eq_card_sep]
  have := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset V))
    (t := ({S | Sep G S} : Finset (Finset V))) (fun v => ({v} : Finset V)) ?_ ?_
  · simpa using this
  · intro v _
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
    exact sep_singleton G v
  · intro v _ w _ h
    exact Finset.singleton_injective h

/-- **Lemma 2.1(f)**: the complete graph attains the upper bound. -/
theorem c_top [Fintype V] : c (⊤ : SimpleGraph V) = 2 ^ Fintype.card V - 1 := by
  classical
  rw [c_eq_card_sep]
  have : ({S | Sep (⊤ : SimpleGraph V) S} : Finset (Finset V)) = Finset.univ.erase ∅ := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
    constructor
    · intro h; exact h.1.ne_empty
    · intro h
      refine ⟨Finset.nonempty_iff_ne_empty.2 h, fun A hA hAne hAS => ?_⟩
      obtain ⟨a, ha⟩ := hAne
      obtain ⟨b, hbS, hbA⟩ : ∃ b ∈ S, b ∉ A := by
        by_contra hcon; push Not at hcon
        exact hAS (Finset.Subset.antisymm hA hcon)
      exact ⟨a, ha, b, hbS, hbA, by simp only [top_adj]; rintro rfl; exact hbA ha⟩
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_finset]

/-! ### Kernel checks on three and four vertices -/

def pa4 (p : ℕ) : Fin 4 := ⟨[0, 0, 1, 0, 1, 2].getD p 0 % 4, Nat.mod_lt _ (by norm_num)⟩
def pb4 (p : ℕ) : Fin 4 := ⟨[1, 2, 2, 3, 3, 3].getD p 0 % 4, Nat.mod_lt _ (by norm_num)⟩

theorem pair_table4 : ∀ i j : Fin 4, i ≠ j → pidx i j < 6 ∧
    ((pa4 (pidx i j) = i ∧ pb4 (pidx i j) = j) ∨ (pa4 (pidx i j) = j ∧ pb4 (pidx i j) = i)) := by
  decide

def m4 (b : ℕ) (i : ℕ) : ℕ := maskOf ((List.range 4).filter (fun j => j ≠ i ∧ b.testBit (pidx i j)))

theorem four_vertex_check : ∀ b < 64, cM (m4 b) 4 ≠ 9 := by
  decide +kernel

open Classical in
noncomputable def code4 (G : SimpleGraph (Fin 4)) : ℕ :=
  maskOf ((List.range 6).filter (fun p => G.Adj (pa4 p) (pb4 p)))

theorem testBit_code4 (G : SimpleGraph (Fin 4)) (q : ℕ) :
    (code4 G).testBit q = true ↔ q < 6 ∧ G.Adj (pa4 q) (pb4 q) := by
  classical
  simp [code4, testBit_maskOf]

theorem code4_lt (G : SimpleGraph (Fin 4)) : code4 G < 64 := by
  apply Nat.lt_pow_two_of_testBit (n := 6)
  intro i hi
  cases h : (code4 G).testBit i
  · rfl
  · have := (testBit_code4 G i).1 h
    omega

theorem m4_code4 (G : SimpleGraph (Fin 4)) :
    ∀ i j : Fin 4, (m4 (code4 G) i).testBit j = true ↔ G.Adj i j := by
  intro i j
  simp only [m4, testBit_maskOf, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨-, hji, hb⟩
    have hij : i ≠ j := fun h => hji (by rw [h])
    obtain ⟨-, htab⟩ := pair_table4 i j hij
    have := ((testBit_code4 G _).1 hb).2
    rcases htab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rwa [h1, h2] at this
    · rw [h1, h2] at this; exact this.symm
  · intro hadj
    have hij : i ≠ j := G.ne_of_adj hadj
    obtain ⟨hlt, htab⟩ := pair_table4 i j hij
    refine ⟨j.2, fun h => hij (Fin.ext h.symm), (testBit_code4 G _).2 ⟨hlt, ?_⟩⟩
    rcases htab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hadj
    · rw [h1, h2]; exact hadj.symm

/-- No graph on four vertices has `c = 9`. -/
theorem c_ne_nine (G : SimpleGraph (Fin 4)) : c G ≠ 9 := by
  rw [c_eq_cM G _ (m4_code4 G)]
  exact four_vertex_check _ (code4_lt G)

def pa3 (p : ℕ) : Fin 3 := ⟨[0, 0, 1].getD p 0 % 3, Nat.mod_lt _ (by norm_num)⟩
def pb3 (p : ℕ) : Fin 3 := ⟨[1, 2, 2].getD p 0 % 3, Nat.mod_lt _ (by norm_num)⟩

theorem pair_table3 : ∀ i j : Fin 3, i ≠ j → pidx i j < 3 ∧
    ((pa3 (pidx i j) = i ∧ pb3 (pidx i j) = j) ∨ (pa3 (pidx i j) = j ∧ pb3 (pidx i j) = i)) := by
  decide

def m3 (b : ℕ) (i : ℕ) : ℕ := maskOf ((List.range 3).filter (fun j => j ≠ i ∧ b.testBit (pidx i j)))

theorem three_vertex_check : ∀ b < 8, cM (m3 b) 3 ≠ 5 := by
  decide +kernel

open Classical in
noncomputable def code3 (G : SimpleGraph (Fin 3)) : ℕ :=
  maskOf ((List.range 3).filter (fun p => G.Adj (pa3 p) (pb3 p)))

theorem testBit_code3 (G : SimpleGraph (Fin 3)) (q : ℕ) :
    (code3 G).testBit q = true ↔ q < 3 ∧ G.Adj (pa3 q) (pb3 q) := by
  classical
  simp [code3, testBit_maskOf]

theorem code3_lt (G : SimpleGraph (Fin 3)) : code3 G < 8 := by
  apply Nat.lt_pow_two_of_testBit (n := 3)
  intro i hi
  cases h : (code3 G).testBit i
  · rfl
  · have := (testBit_code3 G i).1 h
    omega

theorem m3_code3 (G : SimpleGraph (Fin 3)) :
    ∀ i j : Fin 3, (m3 (code3 G) i).testBit j = true ↔ G.Adj i j := by
  intro i j
  simp only [m3, testBit_maskOf, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨-, hji, hb⟩
    have hij : i ≠ j := fun h => hji (by rw [h])
    obtain ⟨-, htab⟩ := pair_table3 i j hij
    have := ((testBit_code3 G _).1 hb).2
    rcases htab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rwa [h1, h2] at this
    · rw [h1, h2] at this; exact this.symm
  · intro hadj
    have hij : i ≠ j := G.ne_of_adj hadj
    obtain ⟨hlt, htab⟩ := pair_table3 i j hij
    refine ⟨j.2, fun h => hij (Fin.ext h.symm), (testBit_code3 G _).2 ⟨hlt, ?_⟩⟩
    rcases htab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hadj
    · rw [h1, h2]; exact hadj.symm

/-- No graph on three vertices has `c = 5`. -/
theorem c_ne_five (G : SimpleGraph (Fin 3)) : c G ≠ 5 := by
  rw [c_eq_cM G _ (m3_code3 G)]
  exact three_vertex_check _ (code3_lt G)

/-! ### Lemma 3.1 -/

theorem InV.bounds {m k : ℕ} (h : InV m k) : T m ≤ k ∧ k ≤ 2 ^ m - 1 := by
  obtain ⟨G, hG, rfl⟩ := h
  have h1 := T_le_c G hG
  have h2 := c_le G
  rw [Fintype.card_fin] at h1 h2
  exact ⟨h1, h2⟩

theorem InLam.bounds {m k : ℕ} (h : InLam m k) : m ≤ k ∧ k ≤ 2 ^ m - 1 := by
  obtain ⟨G, rfl⟩ := h
  have h1 := card_le_c G
  have h2 := c_le G
  rw [Fintype.card_fin] at h1 h2
  exact ⟨h1, h2⟩

theorem V1_iff (k : ℕ) : InV 1 k ↔ k = 1 := by
  constructor
  · intro h; have := h.bounds; simp [T] at this; omega
  · rintro rfl; exact V_1_1

theorem V2_iff (k : ℕ) : InV 2 k ↔ k = 3 := by
  constructor
  · intro h; have := h.bounds; simp [T] at this; omega
  · rintro rfl; exact V_2_3

theorem V3_iff (k : ℕ) : InV 3 k ↔ k = 6 ∨ k = 7 := by
  constructor
  · intro h; have := h.bounds; simp [T] at this; omega
  · rintro (rfl | rfl)
    · exact V_3_6
    · exact V_3_7

theorem V4_iff (k : ℕ) : InV 4 k ↔ 10 ≤ k ∧ k ≤ 15 := by
  constructor
  · intro h; have := h.bounds; simp [T] at this; omega
  · rintro ⟨h1, h2⟩
    interval_cases k
    exacts [V_4_10, V_4_11, V_4_12, V_4_13, V_4_14, V_4_15]

theorem Lam2_iff (k : ℕ) : InLam 2 k ↔ k = 2 ∨ k = 3 := by
  constructor
  · intro h; have := h.bounds; omega
  · rintro (rfl | rfl)
    · exact L_2_2
    · exact L_2_3

theorem Lam3_iff (k : ℕ) : InLam 3 k ↔ k = 3 ∨ k = 4 ∨ k = 6 ∨ k = 7 := by
  constructor
  · intro h
    have hb := h.bounds
    obtain ⟨G, rfl⟩ := h
    have := c_ne_five G
    norm_num at hb
    omega
  · rintro (rfl | rfl | rfl | rfl)
    exacts [L_3_3, L_3_4, L_3_6, L_3_7]

theorem Lam4_iff (k : ℕ) : InLam 4 k ↔ (4 ≤ k ∧ k ≤ 8) ∨ (10 ≤ k ∧ k ≤ 15) := by
  constructor
  · intro h
    have hb := h.bounds
    obtain ⟨G, rfl⟩ := h
    have := c_ne_nine G
    norm_num at hb
    omega
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · interval_cases k
      exacts [L_4_4, L_4_5, L_4_6, L_4_7, L_4_8]
    · interval_cases k
      exacts [L_4_10, L_4_11, L_4_12, L_4_13, L_4_14, L_4_15]

/-! ### Corollary 3.3, Proposition 3.4, Corollary 3.5 -/

theorem inV_path (n : ℕ) (hn : n ≠ 0) : InV n (T n) := by
  have := inV_of (pathGraph n) (connected_pathGraph.2 hn) (Fintype.card_fin n)
  rwa [c_pathGraph] at this

theorem inV_spider (n : ℕ) (hn : 4 ≤ n) : InV n (T n + (n - 3)) := by
  have := inV_of (spiderG n) (spiderG_connected hn) (Fintype.card_fin n)
  rwa [c_spiderG hn] at this

/-- **Corollary 3.3**: for `n ≥ 5`, no value strictly between `T n` and `T n + (n - 3)` is the
value of `c` on a connected graph with `n` vertices. -/
theorem gap_not_mem (n k : ℕ) (h1 : T n < k) (h2 : k < T n + (n - 3)) : ¬ InV n k := by
  rintro ⟨G, hG, rfl⟩
  have := c_gap G hG
  rw [Fintype.card_fin] at this
  omega

/-- **Proposition 3.4**: `V_5 = {15} ∪ [17, 24] ∪ [26, 31]`. -/
theorem V5_iff (k : ℕ) : InV 5 k ↔ k = 15 ∨ (17 ≤ k ∧ k ≤ 24) ∨ (26 ≤ k ∧ k ≤ 31) := by
  constructor
  · intro h
    have hb := h.bounds
    obtain ⟨G, hG, rfl⟩ := h
    have := c_ne_of_five G hG
    simp [T] at hb
    omega
  · rintro (rfl | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact inV_path 5 (by norm_num)
    · exact V5I k h1 (by omega) (by omega)
    · exact V5I k (by omega) h2 (by omega)

/-- **Corollary 3.5**: the values of `c` on connected graphs that are at most `16`. -/
theorem values_le_16 (k : ℕ) (hk : 0 < k) (h16 : k ≤ 16) :
    (∃ n, ∃ G : SimpleGraph (Fin n), G.Connected ∧ c G = k) ↔
      k = 1 ∨ k = 3 ∨ k = 6 ∨ k = 7 ∨ (10 ≤ k ∧ k ≤ 15) := by
  rw [classification k hk]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-! ### Theorem 1.2 for every attainable value -/

theorem minOrder_le_all (k : ℕ) (hk : 0 < k) {n : ℕ} (G : SimpleGraph (Fin n)) (hG : G.Connected)
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

theorem minOrder_of_lt {k m : ℕ} (h1 : 2 ^ m ≤ k) (h2 : k < 2 ^ (m + 1)) (h25 : k ≠ 25) :
    minOrder k = m + 1 := by
  unfold minOrder
  simp only [h25, ↓reduceIte]
  rw [Nat.log_eq_of_pow_le_of_lt_pow h1 h2]

/-- **Theorem 1.2**: for every attainable value `k`, the least order of a connected graph with
`c = k` is `minOrder k`, which is `⌊log₂ k⌋ + 1` except `minOrder 25 = 6`. -/
theorem least_order (k : ℕ) (hk : 0 < k) (hk' : k ∉ ({2, 4, 5, 8, 9, 16} : Finset ℕ)) :
    InV (minOrder k) k ∧
      ∀ n (G : SimpleGraph (Fin n)), G.Connected → c G = k → minOrder k ≤ n := by
  refine ⟨?_, fun n G hG hc => minOrder_le_all k hk G hG hc⟩
  rcases (show k ≤ 16 ∨ 17 ≤ k by omega) with h | h
  · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk'
    interval_cases k
    · rw [minOrder_of_lt (m := 0) (by norm_num) (by norm_num) (by norm_num)]; exact V_1_1
    · omega
    · rw [minOrder_of_lt (m := 1) (by norm_num) (by norm_num) (by norm_num)]; exact V_2_3
    · omega
    · omega
    · rw [minOrder_of_lt (m := 2) (by norm_num) (by norm_num) (by norm_num)]; exact V_3_6
    · rw [minOrder_of_lt (m := 2) (by norm_num) (by norm_num) (by norm_num)]; exact V_3_7
    · omega
    · omega
    · rw [minOrder_of_lt (m := 3) (by norm_num) (by norm_num) (by norm_num)]; exact V_4_10
    · rw [minOrder_of_lt (m := 3) (by norm_num) (by norm_num) (by norm_num)]; exact V_4_11
    · rw [minOrder_of_lt (m := 3) (by norm_num) (by norm_num) (by norm_num)]; exact V_4_12
    · rw [minOrder_of_lt (m := 3) (by norm_num) (by norm_num) (by norm_num)]; exact V_4_13
    · rw [minOrder_of_lt (m := 3) (by norm_num) (by norm_num) (by norm_num)]; exact V_4_14
    · rw [minOrder_of_lt (m := 3) (by norm_num) (by norm_num) (by norm_num)]; exact V_4_15
    · omega
  · exact realize_minOrder k h

/-! ### Proposition 6.1 -/

/-- **Proposition 6.1.** For `n ≥ 6`: `T n` and `T n + (n - 3)` lie in `V_n`, the `n - 4`
integers strictly between them do not, and `[2^(n-1), 2^n - 1] ⊆ V_n`. -/
theorem fixed_order (n : ℕ) (hn : 6 ≤ n) :
    InV n (T n) ∧ InV n (T n + (n - 3)) ∧ (∀ k, T n < k → k < T n + (n - 3) → ¬ InV n k) ∧
      (∀ k, 2 ^ (n - 1) ≤ k → k < 2 ^ n → InV n k) :=
  ⟨inV_path n (by omega), inV_spider n (by omega), fun k h1 h2 => gap_not_mem n k h1 h2,
    fun k h1 h2 => G_all n (by omega) k h1 h2⟩

end ConnectedSets
