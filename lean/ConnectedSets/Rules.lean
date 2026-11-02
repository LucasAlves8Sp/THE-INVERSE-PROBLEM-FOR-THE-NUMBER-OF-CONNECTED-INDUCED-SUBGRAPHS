/-
ConnectedSets/Rules.lean

Counting rules for `c`:
* `c_edgeless`  : the edgeless graph on `V` has `|V|` connected sets;
* `c_unionG`    : `c` is additive on disjoint unions;
* `c_coneG`     : adding a vertex adjacent to everything adds `2^|V|`;
* `c_aconeG`    : adding a vertex adjacent to everything except `u` adds `2^|V| - 2^(|V|-1-deg u)`.
-/
import ConnectedSets.Defs

open Finset

namespace ConnectedSets

variable {V W : Type*}

/-! ### Sep along embeddings -/

theorem sep_map_emb [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} (f : V ↪ W)
    (hf : ∀ a b, H.Adj (f a) (f b) ↔ G.Adj a b) (S : Finset V) :
    Sep H (S.map f) ↔ Sep G S := by
  classical
  constructor
  · rintro ⟨hne, h⟩
    refine ⟨by simpa using hne, ?_⟩
    intro A hA hAne hAS
    obtain ⟨a, ha, b, hb, hbA, hab⟩ := h (A.map f) (Finset.map_subset_map.2 hA)
      (by simpa using hAne) (by simpa using hAS)
    simp only [Finset.mem_map] at ha hb
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    refine ⟨a', ha', b', hb', ?_, (hf a' b').1 hab⟩
    intro hb'A; exact hbA (Finset.mem_map_of_mem f hb'A)
  · rintro ⟨hne, h⟩
    refine ⟨by simpa using hne, ?_⟩
    intro A hA hAne hAS
    set A' := S.filter (fun x => f x ∈ A) with hA'
    have hA'map : A'.map f = A := by
      ext y
      simp only [Finset.mem_map, hA', Finset.mem_filter]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx.2
      · intro hy
        have hyS := hA hy
        simp only [Finset.mem_map] at hyS
        obtain ⟨x, hxS, rfl⟩ := hyS
        exact ⟨x, ⟨hxS, hy⟩, rfl⟩
    have hA'S : A' ⊆ S := Finset.filter_subset _ _
    have hA'ne : A'.Nonempty := by
      rw [← Finset.map_nonempty (f := f), hA'map]; exact hAne
    have hA'S' : A' ≠ S := by
      intro heq; apply hAS; rw [← hA'map, heq]
    obtain ⟨a, ha, b, hb, hbA, hab⟩ := h A' hA'S hA'ne hA'S'
    refine ⟨f a, ?_, f b, Finset.mem_map_of_mem f hb, ?_, (hf a b).2 hab⟩
    · simp only [hA', Finset.mem_filter] at ha; exact ha.2
    · intro hbA'; exact hbA (by simp only [hA', Finset.mem_filter]; exact ⟨hb, hbA'⟩)

/-! ### Edgeless graphs -/

theorem sep_bot_iff [DecidableEq V] (S : Finset V) :
    Sep (⊥ : SimpleGraph V) S ↔ ∃ v, S = {v} := by
  constructor
  · rintro ⟨⟨v, hv⟩, h⟩
    refine ⟨v, ?_⟩
    by_contra hne
    have hsub : ({v} : Finset V) ⊆ S := by simpa using hv
    obtain ⟨a, -, b, -, -, hab⟩ := h {v} hsub (Finset.singleton_nonempty v) (Ne.symm hne)
    exact hab
  · rintro ⟨v, rfl⟩; exact sep_singleton _ v

theorem c_edgeless [Fintype V] [DecidableEq V] : c (⊥ : SimpleGraph V) = Fintype.card V := by
  classical
  rw [c_eq_card_sep]
  have : ({S | Sep (⊥ : SimpleGraph V) S} : Finset (Finset V)) =
      (Finset.univ : Finset V).map ⟨fun v => {v}, Finset.singleton_injective⟩ := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk, sep_bot_iff]
    constructor
    · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩; exact ⟨v, rfl⟩
  rw [this, Finset.card_map, Finset.card_univ]

/-! ### Disjoint union -/

/-- Disjoint union of two graphs, on the sum type. -/
def unionG (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ W) where
  Adj x y := match x, y with
    | .inl a, .inl b => G.Adj a b
    | .inr a, .inr b => H.Adj a b
    | _, _ => False
  symm := ⟨by
    rintro (a | a) (b | b) h
    · exact SimpleGraph.Adj.symm (G := G) h
    · exact h
    · exact h
    · exact SimpleGraph.Adj.symm (G := H) h⟩
  loopless := ⟨by
    rintro (a | a) h
    · exact G.irrefl h
    · exact H.irrefl h⟩

@[simp] theorem unionG_adj_inl_inl (G : SimpleGraph V) (H : SimpleGraph W) (a b : V) :
    (unionG G H).Adj (.inl a) (.inl b) ↔ G.Adj a b := Iff.rfl
@[simp] theorem unionG_adj_inr_inr (G : SimpleGraph V) (H : SimpleGraph W) (a b : W) :
    (unionG G H).Adj (.inr a) (.inr b) ↔ H.Adj a b := Iff.rfl
@[simp] theorem unionG_adj_inl_inr (G : SimpleGraph V) (H : SimpleGraph W) (a : V) (b : W) :
    ¬ (unionG G H).Adj (.inl a) (.inr b) := fun h => h
@[simp] theorem unionG_adj_inr_inl (G : SimpleGraph V) (H : SimpleGraph W) (a : W) (b : V) :
    ¬ (unionG G H).Adj (.inr a) (.inl b) := fun h => h

/-- A connected set of a disjoint union lies on one side. -/
theorem sep_unionG_side [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    {S : Finset (V ⊕ W)} (hS : Sep (unionG G H) S) :
    (∃ S₁ : Finset V, S = S₁.map Function.Embedding.inl) ∨
      (∃ S₂ : Finset W, S = S₂.map Function.Embedding.inr) := by
  classical
  -- if S meets both sides, the left part is a separation with no edges
  by_cases hL : ∀ x ∈ S, x.isLeft
  · left
    refine ⟨Finset.univ.filter (fun x : V => (Sum.inl x : V ⊕ W) ∈ S), ?_⟩
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.inl_apply]
    constructor
    · intro hy
      have := hL y hy
      rcases y with a | b
      · exact ⟨a, hy, rfl⟩
      · simp at this
    · rintro ⟨a, ha, rfl⟩; exact ha
  · push Not at hL
    obtain ⟨x, hxS, hx⟩ := hL
    by_cases hR : ∀ y ∈ S, y.isRight
    · right
      refine ⟨Finset.univ.filter (fun x : W => (Sum.inr x : V ⊕ W) ∈ S), ?_⟩
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.inr_apply]
      constructor
      · intro hy
        have := hR y hy
        rcases y with a | b
        · simp at this
        · exact ⟨b, hy, rfl⟩
      · rintro ⟨b, hb, rfl⟩; exact hb
    · exfalso
      push Not at hR
      obtain ⟨y, hyS, hy⟩ := hR
      set A := S.filter (fun z => z.isLeft) with hA
      have hAS : A ⊆ S := Finset.filter_subset _ _
      have hyA : y ∈ A := by simp [hA, hyS]; simpa using hy
      have hxA : x ∉ A := by simp [hA]; intro _; simpa using hx
      obtain ⟨a, haA, b, hbS, hbA, hab⟩ := hS.2 A hAS ⟨y, hyA⟩ (fun h => hxA (h ▸ hxS))
      simp only [hA, Finset.mem_filter] at haA hbA
      rcases a with a | a <;> rcases b with b | b
      · simp at hbA; exact hbA hbS
      · exact hab
      · simp at haA
      · simp at haA

theorem c_unionG [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) : c (unionG G H) = c G + c H := by
  classical
  rw [c_eq_card_sep, c_eq_card_sep, c_eq_card_sep]
  let eL : Finset V ↪ Finset (V ⊕ W) := ⟨fun S => S.map Function.Embedding.inl, Finset.map_injective _⟩
  let eR : Finset W ↪ Finset (V ⊕ W) := ⟨fun S => S.map Function.Embedding.inr, Finset.map_injective _⟩
  have hL : ∀ S : Finset V, Sep (unionG G H) (S.map Function.Embedding.inl) ↔ Sep G S :=
    sep_map_emb Function.Embedding.inl (fun a b => Iff.rfl)
  have hR : ∀ S : Finset W, Sep (unionG G H) (S.map Function.Embedding.inr) ↔ Sep H S :=
    sep_map_emb Function.Embedding.inr (fun a b => Iff.rfl)
  have heq : ({S | Sep (unionG G H) S} : Finset (Finset (V ⊕ W))) =
      ({S | Sep G S} : Finset (Finset V)).map eL ∪ ({S | Sep H S} : Finset (Finset W)).map eR := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_map]
    constructor
    · intro hS
      rcases sep_unionG_side hS with ⟨S₁, rfl⟩ | ⟨S₂, rfl⟩
      · exact Or.inl ⟨S₁, (hL S₁).1 hS, rfl⟩
      · exact Or.inr ⟨S₂, (hR S₂).1 hS, rfl⟩
    · rintro (⟨S₁, h₁, rfl⟩ | ⟨S₂, h₂, rfl⟩)
      · exact (hL S₁).2 h₁
      · exact (hR S₂).2 h₂
  rw [heq, Finset.card_union_of_disjoint, Finset.card_map, Finset.card_map]
  rw [Finset.disjoint_left]
  intro S hS1 hS2
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and] at hS1 hS2
  obtain ⟨S₁, h₁, rfl⟩ := hS1
  obtain ⟨S₂, h₂, heq'⟩ := hS2
  obtain ⟨v, hv⟩ := h₁.1
  have : (Sum.inl v : V ⊕ W) ∈ eR S₂ := by
    rw [heq']; exact Finset.mem_map_of_mem _ hv
  simp [eR] at this

/-! ### Cones and almost-cones -/

/-- Graph on `Option V`: `K` on `some _`, and `none` adjacent to `some v` iff `p v`. -/
def apexG (K : SimpleGraph V) (p : V → Prop) : SimpleGraph (Option V) where
  Adj x y := match x, y with
    | none, none => False
    | none, some v => p v
    | some v, none => p v
    | some a, some b => K.Adj a b
  symm := ⟨by
    rintro (_ | a) (_ | b) h
    · exact h
    · exact h
    · exact h
    · exact SimpleGraph.Adj.symm (G := K) h⟩
  loopless := ⟨by
    rintro (_ | a) h
    · exact h
    · exact K.irrefl h⟩

@[simp] theorem apexG_adj_some_some (K : SimpleGraph V) (p : V → Prop) (a b : V) :
    (apexG K p).Adj (some a) (some b) ↔ K.Adj a b := Iff.rfl
@[simp] theorem apexG_adj_none_some (K : SimpleGraph V) (p : V → Prop) (v : V) :
    (apexG K p).Adj none (some v) ↔ p v := Iff.rfl
@[simp] theorem apexG_adj_some_none (K : SimpleGraph V) (p : V → Prop) (v : V) :
    (apexG K p).Adj (some v) none ↔ p v := Iff.rfl
@[simp] theorem apexG_adj_none_none (K : SimpleGraph V) (p : V → Prop) :
    ¬ (apexG K p).Adj none none := fun h => h

/-- The cone over `K`. -/
def coneG (K : SimpleGraph V) : SimpleGraph (Option V) := apexG K (fun _ => True)

/-- The almost-cone over `K` missing `u`. -/
def aconeG (K : SimpleGraph V) (u : V) : SimpleGraph (Option V) := apexG K (fun v => v ≠ u)

/-- Sets avoiding the apex. -/
theorem sep_apex_some_iff [DecidableEq V] (K : SimpleGraph V) (p : V → Prop) (S : Finset V) :
    Sep (apexG K p) (S.map Function.Embedding.some) ↔ Sep K S :=
  sep_map_emb Function.Embedding.some (fun a b => Iff.rfl) S

/-- Sets containing the apex are of the form `insert none (U.map some)`. -/
theorem eq_insert_none_map [Fintype V] [DecidableEq V] {S : Finset (Option V)} (h : none ∈ S) :
    S = insert none ((Finset.univ.filter (fun v => some v ∈ S)).map Function.Embedding.some) := by
  classical
  ext x
  rcases x with _ | v
  · simp [h]
  · simp

theorem eq_map_some [Fintype V] [DecidableEq V] {S : Finset (Option V)} (h : none ∉ S) :
    S = (Finset.univ.filter (fun v => some v ∈ S)).map Function.Embedding.some := by
  classical
  ext x
  rcases x with _ | v
  · simp [h]
  · simp

/-- In an apex graph, inserting vertices adjacent to the apex keeps connectivity. -/
theorem sep_apex_insert_all [DecidableEq V] (K : SimpleGraph V) (p : V → Prop) (U : Finset V)
    (hU : ∀ v ∈ U, p v) : Sep (apexG K p) (insert none (U.map Function.Embedding.some)) := by
  classical
  induction U using Finset.induction_on with
  | empty => simpa using sep_singleton (apexG K p) none
  | insert v U hvU ih =>
    have ih' := ih (fun w hw => hU w (Finset.mem_insert_of_mem hw))
    have hpv := hU v (Finset.mem_insert_self v U)
    have hset : insert none ((insert v U).map Function.Embedding.some) =
        insert (some v) (insert none (U.map Function.Embedding.some)) := by
      ext x; simp only [Finset.map_insert, Finset.mem_insert, Function.Embedding.some_apply]; tauto
    rw [hset]
    apply sep_insert ih'
    · simp [hvU]
    · exact ⟨none, Finset.mem_insert_self _ _, hpv⟩

open Classical in
/-- Counting for apex graphs: split by whether the apex is in the set. -/
theorem c_apexG_split [Fintype V] [DecidableEq V] (K : SimpleGraph V) (p : V → Prop) :
    c (apexG K p) = c K + #{U : Finset V | Sep (apexG K p) (insert none (U.map Function.Embedding.some))} := by
  classical
  rw [c_eq_card_sep, c_eq_card_sep]
  rw [← Finset.card_filter_add_card_filter_not (p := fun S : Finset (Option V) => none ∈ S)]
  rw [add_comm]
  congr 1
  · -- sets avoiding the apex
    apply Finset.card_bij (fun S _ => Finset.univ.filter (fun v => some v ∈ S))
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      rw [← sep_apex_some_iff K p, ← eq_map_some hS.2]
      exact hS.1
    · intro S hS S' hS' h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS hS'
      rw [eq_map_some hS.2, eq_map_some hS'.2, h]
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
      refine ⟨U.map Function.Embedding.some, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨(sep_apex_some_iff K p U).2 hU, by simp⟩
      · ext v; simp
  · -- sets containing the apex
    apply Finset.card_bij (fun S _ => Finset.univ.filter (fun v => some v ∈ S))
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
      rw [← eq_insert_none_map hS.2]
      exact hS.1
    · intro S hS S' hS' h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS hS'
      rw [eq_insert_none_map hS.2, eq_insert_none_map hS'.2, h]
    · intro U hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
      refine ⟨insert none (U.map Function.Embedding.some), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hU, Finset.mem_insert_self _ _⟩
      · ext v; simp

theorem c_coneG [Fintype V] [DecidableEq V] (K : SimpleGraph V) :
    c (coneG K) = 2 ^ Fintype.card V + c K := by
  classical
  unfold coneG
  rw [c_apexG_split, add_comm]
  congr 1
  rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_finset]
  intro U _
  exact sep_apex_insert_all K _ U (fun _ _ => trivial)

/-- The apex-containing set is connected unless `u` is in it without neighbours in it. -/
theorem sep_acone_iff [DecidableEq V] (K : SimpleGraph V) (u : V) (U : Finset V) :
    Sep (aconeG K u) (insert none (U.map Function.Embedding.some)) ↔
      ¬ (u ∈ U ∧ ∀ y ∈ U, ¬ K.Adj u y) := by
  classical
  unfold aconeG
  constructor
  · rintro hS ⟨huU, hno⟩
    have hsub : ({some u} : Finset (Option V)) ⊆ insert none (U.map Function.Embedding.some) := by
      simp [huU]
    have hne : ({some u} : Finset (Option V)) ≠ insert none (U.map Function.Embedding.some) := by
      intro h
      have : (none : Option V) ∈ ({some u} : Finset (Option V)) := by rw [h]; simp
      simp at this
    obtain ⟨a, ha, b, hb, hbA, hab⟩ := hS.2 _ hsub (Finset.singleton_nonempty _) hne
    rw [Finset.mem_singleton] at ha
    subst ha
    rcases b with _ | b
    · exact hab rfl
    · have hbU : b ∈ U := by simpa using hb
      exact hno b hbU hab
  · intro hgood
    -- all vertices other than u are adjacent to the apex
    have hbase := sep_apex_insert_all K (fun v => v ≠ u) (U.erase u) (fun v hv => Finset.ne_of_mem_erase hv)
    by_cases huU : u ∈ U
    · have hset : insert none (U.map Function.Embedding.some) =
          insert (some u) (insert none ((U.erase u).map Function.Embedding.some)) := by
        ext x
        rcases x with _ | v
        · simp
        · simp only [Finset.mem_insert, Finset.mem_map, Function.Embedding.some_apply, reduceCtorEq,
            false_or, Option.some.injEq, Finset.mem_erase]
          constructor
          · rintro ⟨y, hy, rfl⟩
            by_cases hyu : y = u
            · exact Or.inl hyu
            · exact Or.inr ⟨y, ⟨hyu, hy⟩, rfl⟩
          · rintro (rfl | ⟨y, ⟨-, hy⟩, rfl⟩)
            · exact ⟨_, huU, rfl⟩
            · exact ⟨y, hy, rfl⟩
      rw [hset]
      apply sep_insert hbase
      · simp
      · push Not at hgood
        obtain ⟨y, hyU, hy⟩ := hgood huU
        have hyu : y ≠ u := fun h => K.irrefl (h ▸ hy)
        refine ⟨some y, ?_, ?_⟩
        · simp [hyU, hyu]
        · exact hy.symm
    · have hset : U.erase u = U := Finset.erase_eq_of_notMem huU
      rw [hset] at hbase
      exact hbase

open Classical in
theorem card_bad [Fintype V] [DecidableEq V] (K : SimpleGraph V) (u : V) (N : Finset V)
    (hN : ∀ y, K.Adj u y ↔ y ∈ N) :
    #{U : Finset V | u ∈ U ∧ ∀ y ∈ U, ¬ K.Adj u y} = 2 ^ (Fintype.card V - 1 - #N) := by
  classical
  have huN : u ∉ N := fun h => K.irrefl ((hN u).2 h)
  set R := (Finset.univ \ insert u N) with hR
  have hRcard : #R = Fintype.card V - 1 - #N := by
    rw [hR, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_insert_of_notMem huN,
      Finset.card_univ]
    omega
  rw [← hRcard, ← Finset.card_powerset]
  apply Finset.card_bij (fun U _ => U.erase u)
  · intro U hU
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU
    rw [Finset.mem_powerset]
    intro y hy
    rw [hR, Finset.mem_sdiff, Finset.mem_insert]
    refine ⟨Finset.mem_univ _, ?_⟩
    rintro (rfl | hyN)
    · exact (Finset.notMem_erase _ _) hy
    · exact hU.2 y (Finset.mem_of_mem_erase hy) ((hN y).2 hyN)
  · intro U hU U' hU' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hU hU'
    rw [← Finset.insert_erase hU.1, ← Finset.insert_erase hU'.1, h]
  · intro Y hY
    rw [Finset.mem_powerset] at hY
    have huY : u ∉ Y := by
      intro h; have := hY h; simp [hR] at this
    refine ⟨insert u Y, ?_, by simp [huY]⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Finset.mem_insert_self _ _, ?_⟩
    intro y hy hadj
    rcases Finset.mem_insert.1 hy with rfl | hyY
    · exact K.irrefl hadj
    · have := hY hyY
      simp only [hR, Finset.mem_sdiff, Finset.mem_insert, not_or] at this
      exact this.2.2 ((hN y).1 hadj)

theorem c_aconeG [Fintype V] [DecidableEq V] (K : SimpleGraph V) (u : V) (N : Finset V)
    (hN : ∀ y, K.Adj u y ↔ y ∈ N) :
    c (aconeG K u) + 2 ^ (Fintype.card V - 1 - #N) = c K + 2 ^ Fintype.card V := by
  classical
  have hsplit := c_apexG_split K (fun v => v ≠ u)
  have hcount : #{U : Finset V | Sep (apexG K (fun v => v ≠ u)) (insert none (U.map Function.Embedding.some))}
      + 2 ^ (Fintype.card V - 1 - #N) = 2 ^ Fintype.card V := by
    rw [← card_bad K u N hN]
    rw [← Fintype.card_finset, ← Finset.card_univ]
    rw [← Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Finset V)))
      (p := fun U => Sep (apexG K (fun v => v ≠ u)) (insert none (U.map Function.Embedding.some)))]
    congr 1
    apply congrArg
    ext U
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := sep_acone_iff K u U
    unfold aconeG at this
    rw [this]
    tauto
  unfold aconeG
  omega

/-! ### Connectivity of cones and almost-cones -/

theorem coneG_connected (K : SimpleGraph V) : (coneG K).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨none, ?_⟩
  rintro (_ | v)
  · rfl
  · exact SimpleGraph.Adj.reachable (show (coneG K).Adj none (some v) from trivial)

theorem aconeG_connected (K : SimpleGraph V) (u ℓ : V) (hℓ : K.Adj ℓ u) :
    (aconeG K u).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨none, ?_⟩
  have hℓu : ℓ ≠ u := K.ne_of_adj hℓ
  rintro (_ | v)
  · rfl
  · by_cases hv : v = u
    · subst hv
      have h1 : (aconeG K v).Adj none (some ℓ) := hℓu
      have h2 : (aconeG K v).Adj (some ℓ) (some v) := hℓ
      exact h1.reachable.trans h2.reachable
    · exact SimpleGraph.Adj.reachable (show (aconeG K u).Adj none (some v) from hv)

end ConnectedSets
