/-
ConnectedSets/Five.lean

No connected graph on five vertices has c = 16 or c = 25.  This is checked in the kernel over
all 2^10 graphs on `Fin 5`, given by edge codes, through the verified checker.
-/
import ConnectedSets.Checker

open Finset

namespace ConnectedSets

/-- Index of the unordered pair `{i, j}` in graph6 order: (0,1),(0,2),(1,2),(0,3),... -/
def pidx (i j : ℕ) : ℕ := if i < j then j * (j - 1) / 2 + i else i * (i - 1) / 2 + j

/-- Endpoints of the pair with index `p` (for `p < 10`). -/
def pa (p : ℕ) : Fin 5 := ⟨[0, 0, 1, 0, 1, 2, 0, 1, 2, 3].getD p 0 % 5, Nat.mod_lt _ (by norm_num)⟩
def pb (p : ℕ) : Fin 5 := ⟨[1, 2, 2, 3, 3, 3, 4, 4, 4, 4].getD p 0 % 5, Nat.mod_lt _ (by norm_num)⟩

theorem pair_table : ∀ i j : Fin 5, i ≠ j → pidx i j < 10 ∧
    ((pa (pidx i j) = i ∧ pb (pidx i j) = j) ∨ (pa (pidx i j) = j ∧ pb (pidx i j) = i)) := by
  decide

/-- Bitmask of a list of positions. -/
def maskOf (L : List ℕ) : ℕ := L.foldl (fun acc j => acc ||| 2 ^ j) 0

theorem testBit_foldl_or (L : List ℕ) (acc q : ℕ) :
    (L.foldl (fun acc j => acc ||| 2 ^ j) acc).testBit q = true ↔ acc.testBit q = true ∨ q ∈ L := by
  induction L generalizing acc with
  | nil => simp
  | cons x L ih =>
    simp only [List.foldl_cons, ih, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow,
      decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro ((h | rfl) | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr h)
    · rintro (h | rfl | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr rfl)
      · exact Or.inr h

theorem testBit_maskOf (L : List ℕ) (q : ℕ) : (maskOf L).testBit q = true ↔ q ∈ L := by
  simp [maskOf, testBit_foldl_or]

/-- Neighbourhood masks of the graph on `Fin 5` with edge code `b`. -/
def m5 (b : ℕ) (i : ℕ) : ℕ := maskOf ((List.range 5).filter (fun j => j ≠ i ∧ b.testBit (pidx i j)))

/-! The kernel check over all 1024 edge codes, in eight chunks of 128 codes. -/

theorem five_vertex_check_0 :
    ∀ r < 128, connM (m5 (128 * 0 + r)) 5 31 = true →
      cM (m5 (128 * 0 + r)) 5 ≠ 16 ∧ cM (m5 (128 * 0 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_1 :
    ∀ r < 128, connM (m5 (128 * 1 + r)) 5 31 = true →
      cM (m5 (128 * 1 + r)) 5 ≠ 16 ∧ cM (m5 (128 * 1 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_2 :
    ∀ r < 128, connM (m5 (128 * 2 + r)) 5 31 = true →
      cM (m5 (128 * 2 + r)) 5 ≠ 16 ∧ cM (m5 (128 * 2 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_3 :
    ∀ r < 128, connM (m5 (128 * 3 + r)) 5 31 = true →
      cM (m5 (128 * 3 + r)) 5 ≠ 16 ∧ cM (m5 (128 * 3 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_4 :
    ∀ r < 128, connM (m5 (128 * 4 + r)) 5 31 = true →
      cM (m5 (128 * 4 + r)) 5 ≠ 16 ∧ cM (m5 (128 * 4 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_5 :
    ∀ r < 128, connM (m5 (128 * 5 + r)) 5 31 = true →
      cM (m5 (128 * 5 + r)) 5 ≠ 16 ∧ cM (m5 (128 * 5 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_6 :
    ∀ r < 128, connM (m5 (128 * 6 + r)) 5 31 = true →
      cM (m5 (128 * 6 + r)) 5 ≠ 16 ∧ cM (m5 (128 * 6 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_7 :
    ∀ r < 128, connM (m5 (128 * 7 + r)) 5 31 = true →
      cM (m5 (128 * 7 + r)) 5 ≠ 16 ∧ cM (m5 (128 * 7 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check :
    ∀ b < 1024, connM (m5 b) 5 31 = true → cM (m5 b) 5 ≠ 16 ∧ cM (m5 b) 5 ≠ 25 := by
  intro b hb
  have hdecomp : b = 128 * (b / 128) + b % 128 := (Nat.div_add_mod b 128).symm
  have hr : b % 128 < 128 := Nat.mod_lt _ (by norm_num)
  have hq : b / 128 < 8 := by omega
  rw [hdecomp]
  interval_cases (b / 128)
  · exact five_vertex_check_0 _ hr
  · exact five_vertex_check_1 _ hr
  · exact five_vertex_check_2 _ hr
  · exact five_vertex_check_3 _ hr
  · exact five_vertex_check_4 _ hr
  · exact five_vertex_check_5 _ hr
  · exact five_vertex_check_6 _ hr
  · exact five_vertex_check_7 _ hr

open Classical in
/-- The edge code of a graph on `Fin 5`. -/
noncomputable def code5 (G : SimpleGraph (Fin 5)) : ℕ :=
  maskOf ((List.range 10).filter (fun p => G.Adj (pa p) (pb p)))

theorem testBit_code5 (G : SimpleGraph (Fin 5)) (q : ℕ) :
    (code5 G).testBit q = true ↔ q < 10 ∧ G.Adj (pa q) (pb q) := by
  classical
  simp [code5, testBit_maskOf]

theorem code5_lt (G : SimpleGraph (Fin 5)) : code5 G < 1024 := by
  apply Nat.lt_pow_two_of_testBit (n := 10)
  intro i hi
  cases h : (code5 G).testBit i
  · rfl
  · have := (testBit_code5 G i).1 h
    omega

theorem m5_code5 (G : SimpleGraph (Fin 5)) :
    ∀ i j : Fin 5, (m5 (code5 G) i).testBit j = true ↔ G.Adj i j := by
  intro i j
  simp only [m5, testBit_maskOf, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨-, hji, hb⟩
    have hij : i ≠ j := fun h => hji (by rw [h])
    obtain ⟨-, htab⟩ := pair_table i j hij
    have := ((testBit_code5 G _).1 hb).2
    rcases htab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rwa [h1, h2] at this
    · rw [h1, h2] at this; exact this.symm
  · intro hadj
    have hij : i ≠ j := G.ne_of_adj hadj
    obtain ⟨hlt, htab⟩ := pair_table i j hij
    refine ⟨j.2, fun h => hij (Fin.ext h.symm), (testBit_code5 G _).2 ⟨hlt, ?_⟩⟩
    rcases htab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]; exact hadj
    · rw [h1, h2]; exact hadj.symm

/-- No connected graph on five vertices has 16 or 25 connected sets. -/
theorem c_ne_of_five (G : SimpleGraph (Fin 5)) (hG : G.Connected) : c G ≠ 16 ∧ c G ≠ 25 := by
  have ha := m5_code5 G
  have hconn := (connected_iff_connM G _ ha).1 hG
  rw [c_eq_cM G _ ha]
  exact five_vertex_check _ (code5_lt G) hconn

end ConnectedSets
