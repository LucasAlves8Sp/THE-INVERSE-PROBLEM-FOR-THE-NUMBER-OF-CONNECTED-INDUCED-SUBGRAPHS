/-
ConnectedSets/Extras.lean

Further statements of the paper:
* `Lam5_ne_25` : `25 ∉ Λ_5` (Remark 4.5), by a kernel check over all `2^10` labeled graphs on
  five vertices;
* `c_star` : the star `K_(1,d)` (the cone over `d` isolated vertices) has `c = 2^d + d`
  (Section 1 and Example 2.2(i));
* `c_nearCone_two_path` : Example 4.7, `c (N(2, P_4)) = 128` on `8` vertices.
-/
import ConnectedSets.Small

open Finset SimpleGraph

namespace ConnectedSets

/-! ### `25 ∉ Λ_5` -/

theorem five_vertex_check_ne25_0 :
    ∀ r < 128, cM (m5 (128 * 0 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_ne25_1 :
    ∀ r < 128, cM (m5 (128 * 1 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_ne25_2 :
    ∀ r < 128, cM (m5 (128 * 2 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_ne25_3 :
    ∀ r < 128, cM (m5 (128 * 3 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_ne25_4 :
    ∀ r < 128, cM (m5 (128 * 4 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_ne25_5 :
    ∀ r < 128, cM (m5 (128 * 5 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_ne25_6 :
    ∀ r < 128, cM (m5 (128 * 6 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_ne25_7 :
    ∀ r < 128, cM (m5 (128 * 7 + r)) 5 ≠ 25 := by
  decide +kernel

theorem five_vertex_check_ne25 : ∀ b < 1024, cM (m5 b) 5 ≠ 25 := by
  intro b hb
  have hdecomp : b = 128 * (b / 128) + b % 128 := (Nat.div_add_mod b 128).symm
  have hr : b % 128 < 128 := Nat.mod_lt _ (by norm_num)
  have hq : b / 128 < 8 := by omega
  rw [hdecomp]
  interval_cases (b / 128)
  · exact five_vertex_check_ne25_0 _ hr
  · exact five_vertex_check_ne25_1 _ hr
  · exact five_vertex_check_ne25_2 _ hr
  · exact five_vertex_check_ne25_3 _ hr
  · exact five_vertex_check_ne25_4 _ hr
  · exact five_vertex_check_ne25_5 _ hr
  · exact five_vertex_check_ne25_6 _ hr
  · exact five_vertex_check_ne25_7 _ hr

/-- **Remark 4.5**: no graph on five vertices, connected or not, has `25` connected sets. -/
theorem Lam5_ne_25 : ¬ InLam 5 25 := by
  rintro ⟨G, hG⟩
  rw [c_eq_cM G _ (m5_code5 G)] at hG
  exact five_vertex_check_ne25 _ (code5_lt G) hG

/-! ### Stars and Example 4.7 -/

/-- The star `K_(1,d)` has `2^d + d` connected sets. -/
theorem c_star (d : ℕ) : c (coneG (⊥ : SimpleGraph (Fin d))) = 2 ^ d + d := by
  rw [c_coneG, c_edgeless, Fintype.card_fin]

/-- **Example 4.7**: the near-cone `N(2, P_4)` is a connected graph with `8` vertices and
`128` connected sets. -/
theorem c_nearCone_two_path :
    (nearCone 2 (pathGraph 4)).Connected ∧ Fintype.card (Option (Option (Fin 2) ⊕ Fin 4)) = 8 ∧
      c (nearCone 2 (pathGraph 4)) = 128 := by
  refine ⟨nearCone_connected 2 (by norm_num) _, by simp, ?_⟩
  have h := c_nearCone 2 (pathGraph 4)
  rw [c_pathGraph] at h
  norm_num [T] at h
  omega

end ConnectedSets
