/-
ConnectedSets/Gap.lean

The gap above the path (Proposition 3.2 of the paper, in the form of a dichotomy):
a connected set `S` with `s` elements has either exactly `T s` connected subsets, or at least
`T s + (s - 3)` of them.

Notation, for a graph `G` and finite sets of vertices:
* `NS G S` : the number of connected subsets of `S` (connected sets of `G` contained in `S`);
* `AS G S w` : the number of those containing the vertex `w`.

A vertex `y` of a connected set `S` is an *end* of `S` if `AS G S y = #S`, that is, if `S` has
exactly one connected subset containing `y` of each size. The proof shows:
* an end forces `NS G S = T #S` (`NS_eq_T_of_end`);
* if `NS G S = T #S`, every vertex `w` with `S.erase w` connected is an end (`end_of_tight`);
* an end gives an enumeration `φ 0 = y, φ 1, …` of `S` in which consecutive vertices are
  adjacent (`chain_of_end`);
* adding a vertex to a set with `NS = T` that does not create a set with `NS = T` adds at least
  `2 #S - 3` connected sets (`attach_bound`).
-/
import ConnectedSets.Defs

open Finset

namespace ConnectedSets

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidablePred (Sep G)]

/-- The number of connected subsets of `S`. -/
def NS (S : Finset V) : ℕ := #{X ∈ S.powerset | Sep G X}

/-- The number of connected subsets of `S` containing `w`. -/
def AS (S : Finset V) (w : V) : ℕ := #{X ∈ S.powerset | Sep G X ∧ w ∈ X}

variable {G}

omit [DecidableEq V] in
theorem NS_empty : NS G ∅ = 0 := by
  unfold NS
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro X hX hsep
  rw [Finset.mem_powerset, Finset.subset_empty] at hX
  subst hX
  exact Finset.not_nonempty_empty hsep.1

/-- Splitting the connected subsets of `S` according to whether they contain `w`. -/
theorem NS_decomp (S : Finset V) (w : V) :
    NS G S = NS G (S.erase w) + AS G S w := by
  unfold NS AS
  rw [← Finset.card_filter_add_card_filter_not (s := {X ∈ S.powerset | Sep G X}) (fun X => w ∈ X),
    add_comm]
  congr 2
  · ext X
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]
    tauto
  · ext X
    simp only [Finset.mem_filter, Finset.mem_powerset]
    tauto

/-- A connected set `S` has at least `T #S` connected subsets. -/
theorem T_le_NS {S : Finset V} (hS : Sep G S) : T #S ≤ NS G S :=
  T_le_card_sep_subsets G #S S hS rfl

/-- A connected set `S` has at least `#S` connected subsets containing a given vertex. -/
theorem card_le_AS {S : Finset V} (hS : Sep G S) {w : V} (hw : w ∈ S) : #S ≤ AS G S w := by
  unfold AS
  set F := {X ∈ S.powerset | Sep G X ∧ w ∈ X} with hF
  have hsurj : Finset.Icc 1 #S ⊆ F.image Finset.card := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨X, hXS, hX, hwX, hXt⟩ := exists_sep_card hS hw t ht.1 ht.2
    exact Finset.mem_image.2 ⟨X, by simp [hF, hXS, hX, hwX], hXt⟩
  have := Finset.card_le_card hsurj
  simp only [Nat.card_Icc, add_tsub_cancel_right] at this
  exact this.trans Finset.card_image_le

/-- A vertex with two neighbours in `S` lies in at least `#S + 1` connected subsets. -/
theorem succ_le_AS_of_two {S : Finset V} (hS : Sep G S) {w a b : V} (hw : w ∈ S) (ha : a ∈ S)
    (hb : b ∈ S) (hab : a ≠ b) (hwa : G.Adj w a) (hwb : G.Adj w b) : #S + 1 ≤ AS G S w := by
  unfold AS
  set F := {X ∈ S.powerset | Sep G X ∧ w ∈ X} with hF
  have hwa' : w ≠ a := G.ne_of_adj hwa
  have hwb' : w ≠ b := G.ne_of_adj hwb
  have hpa : ({w, a} : Finset V) ∈ F := by
    simp only [hF, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton,
      true_or, and_true]
    refine ⟨Finset.insert_subset hw (Finset.singleton_subset_iff.2 ha), ?_⟩
    have := sep_insert (sep_singleton G a) (b := w) (by simpa using hwa') ⟨a, by simp, hwa.symm⟩
    simpa [Finset.insert_comm] using this
  have hpb : ({w, b} : Finset V) ∈ F.erase {w, a} := by
    refine Finset.mem_erase.2 ⟨?_, ?_⟩
    · intro h
      have : b ∈ ({w, a} : Finset V) := by rw [← h]; simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h1 | h1
      · exact hwb' h1.symm
      · exact hab h1.symm
    · simp only [hF, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert,
        Finset.mem_singleton, true_or, and_true]
      refine ⟨Finset.insert_subset hw (Finset.singleton_subset_iff.2 hb), ?_⟩
      have := sep_insert (sep_singleton G b) (b := w) (by simpa using hwb') ⟨b, by simp, hwb.symm⟩
      simpa [Finset.insert_comm] using this
  have hsurj : Finset.Icc 1 #S ⊆ (F.erase {w, a}).image Finset.card := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    by_cases ht2 : t = 2
    · subst ht2
      refine Finset.mem_image.2 ⟨{w, b}, hpb, ?_⟩
      rw [Finset.card_pair hwb']
    · obtain ⟨X, hXS, hX, hwX, hXt⟩ := exists_sep_card hS hw t ht.1 ht.2
      refine Finset.mem_image.2 ⟨X, Finset.mem_erase.2 ⟨?_, by simp [hF, hXS, hX, hwX]⟩, hXt⟩
      rintro rfl
      rw [Finset.card_pair hwa'] at hXt
      exact ht2 hXt.symm
  have h1 := Finset.card_le_card hsurj
  simp only [Nat.card_Icc, add_tsub_cancel_right] at h1
  have h2 := h1.trans Finset.card_image_le
  rw [Finset.card_erase_of_mem hpa] at h2
  have : 1 ≤ #F := Finset.card_pos.2 ⟨_, hpa⟩
  omega

omit [DecidablePred (Sep G)] in
/-- Removing a vertex with at most one neighbour from a connected set with at least two
elements leaves a connected set. -/
theorem sep_erase_of_leaf {X : Finset V} (hX : Sep G X) {w x : V} (hw : w ∈ X) (hx : x ∈ X)
    (hxw : x ≠ w) (huniq : ∀ z ∈ X, G.Adj w z → z = x) : Sep G (X.erase w) := by
  refine ⟨⟨x, Finset.mem_erase.2 ⟨hxw, hx⟩⟩, ?_⟩
  intro A hA hAne hAX
  have hwA : w ∉ A := fun h => by simpa using hA h
  have hAX' : A ⊆ X := hA.trans (Finset.erase_subset w X)
  have hAneX : A ≠ X := fun h => hwA (h ▸ hw)
  obtain ⟨a, ha, b, hb, hbA, hab⟩ := hX.2 A hAX' hAne hAneX
  by_cases hbw : b = w
  · subst hbw
    have hax : a = x := huniq a (hAX' ha) hab.symm
    subst hax
    -- use the set `insert b A`
    have hins : insert b A ⊆ X := Finset.insert_subset hw hAX'
    have hinsne : insert b A ≠ X := by
      intro h
      apply hAX
      rw [← h, Finset.erase_insert hwA]
    obtain ⟨a', ha', b', hb', hb'A, hab'⟩ := hX.2 (insert b A) hins (Finset.insert_nonempty _ _) hinsne
    rcases Finset.mem_insert.1 ha' with h | h
    · subst h
      have := huniq b' hb' hab'
      subst this
      exact absurd (Finset.mem_insert_of_mem ha) hb'A
    · refine ⟨a', h, b', Finset.mem_erase.2 ⟨?_, hb'⟩, fun h' => hb'A (Finset.mem_insert_of_mem h'),
        hab'⟩
      rintro rfl
      exact hb'A (Finset.mem_insert_self _ _)
  · exact ⟨a, ha, b, Finset.mem_erase.2 ⟨hbw, hb⟩, hbA, hab⟩

/-- A pendant vertex: if `w` has the unique neighbour `x` in the connected set `S`, then
`S.erase w` is connected and `AS G S w = AS G (S.erase w) x + 1`. -/
theorem AS_pendant {S : Finset V} (hS : Sep G S) {w x : V} (hw : w ∈ S) (hx : x ∈ S)
    (hadj : G.Adj w x) (huniq : ∀ z ∈ S, G.Adj w z → z = x) :
    Sep G (S.erase w) ∧ AS G S w = AS G (S.erase w) x + 1 := by
  have hxw : x ≠ w := (G.ne_of_adj hadj).symm
  refine ⟨sep_erase_of_leaf hS hw hx hxw huniq, ?_⟩
  unfold AS
  set F := {X ∈ S.powerset | Sep G X ∧ w ∈ X} with hF
  set F' := {Z ∈ (S.erase w).powerset | Sep G Z ∧ x ∈ Z} with hF'
  have hsplit : F = insert {w} (F.erase {w}) := (Finset.insert_erase (by
    simp [hF, hw, sep_singleton])).symm
  rw [hsplit, Finset.card_insert_of_notMem (Finset.notMem_erase _ _)]
  congr 1
  symm
  apply Finset.card_nbij' (fun Z => insert w Z) (fun Y => Y.erase w)
  · intro Z hZ
    simp only [hF', Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_powerset] at hZ
    obtain ⟨hZS, hZ, hxZ⟩ := hZ
    have hwZ : w ∉ Z := fun h => by simpa using hZS h
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff, hF, Finset.coe_filter,
      Set.mem_ofPred_eq, Finset.mem_powerset]
    refine ⟨⟨Finset.insert_subset hw (hZS.trans (Finset.erase_subset _ _)),
      sep_insert hZ hwZ ⟨x, hxZ, hadj.symm⟩, Finset.mem_insert_self _ _⟩, ?_⟩
    intro h
    have : x ∈ ({w} : Finset V) := by rw [← h]; exact Finset.mem_insert_of_mem hxZ
    exact hxw (Finset.mem_singleton.1 this)
  · intro Y hY
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff, hF, Finset.coe_filter,
      Set.mem_ofPred_eq, Finset.mem_powerset] at hY
    obtain ⟨⟨hYS, hY, hwY⟩, hYw⟩ := hY
    -- `w` has a neighbour in `Y`, which must be `x`
    have hYne : {w} ≠ Y := fun h => hYw h.symm
    obtain ⟨a, ha, b, hbY, hbw, hab⟩ :=
      hY.2 {w} (Finset.singleton_subset_iff.2 hwY) (Finset.singleton_nonempty w) hYne
    rw [Finset.mem_singleton] at ha
    subst ha
    have hbx : b = x := huniq b (hYS hbY) hab
    subst hbx
    simp only [hF', Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_powerset]
    refine ⟨Finset.erase_subset_erase _ hYS, sep_erase_of_leaf hY hwY hbY hxw
      (fun z hz h => huniq z (hYS hz) h), Finset.mem_erase.2 ⟨hxw, hbY⟩⟩
  · intro Z hZ
    simp only [hF', Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_powerset] at hZ
    have hwZ : w ∉ Z := fun h => by simpa using hZ.1 h
    exact Finset.erase_insert hwZ
  · intro Y hY
    simp only [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff, hF, Finset.coe_filter,
      Set.mem_ofPred_eq, Finset.mem_powerset] at hY
    exact Finset.insert_erase hY.1.2.2

/-! ### Ends -/

/-- An end forces the minimum: if `AS G S y = #S`, then `NS G S = T #S`. -/
theorem NS_eq_T_of_end : ∀ s (S : Finset V) (y : V), Sep G S → y ∈ S → #S = s →
    AS G S y = s → NS G S = T s := by
  intro s
  induction s with
  | zero => intro S y _ hy hs _; exact absurd hs (Finset.card_ne_zero.2 ⟨y, hy⟩)
  | succ s ih =>
    intro S y hS hy hs hA
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
      rw [Finset.mem_singleton] at hy
      subst hy
      rw [NS_decomp _ y, hA, Finset.erase_singleton, NS_empty]
      rfl
    -- `y` has a neighbour `b` in `S`, and it is unique
    have hne : ({y} : Finset V) ≠ S := by
      intro h; rw [← h, Finset.card_singleton] at hs; omega
    obtain ⟨a, ha, b, hbS, hby, hab⟩ :=
      hS.2 {y} (Finset.singleton_subset_iff.2 hy) (Finset.singleton_nonempty y) hne
    rw [Finset.mem_singleton] at ha
    subst ha
    rw [Finset.mem_singleton] at hby
    have huniq : ∀ z ∈ S, G.Adj a z → z = b := by
      intro z hz hza
      by_contra hzb
      have := succ_le_AS_of_two hS hy hbS hz (Ne.symm hzb) hab hza
      omega
    obtain ⟨hS', hA'⟩ := AS_pendant hS hy hbS hab huniq
    have hcard : #(S.erase a) = s := by rw [Finset.card_erase_of_mem hy, hs]; rfl
    have hb' : b ∈ S.erase a := Finset.mem_erase.2 ⟨hby, hbS⟩
    have := ih (S.erase a) b hS' hb' hcard (by omega)
    rw [NS_decomp S a, this, hA, T_succ]

/-- If `NS G S = T #S` and `S.erase w` is connected, then `w` is an end of `S`. -/
theorem end_of_tight {S : Finset V} {w : V} (hS : Sep G S) (hw : w ∈ S) (hS' : Sep G (S.erase w))
    (ht : NS G S = T #S) : AS G S w = #S := by
  have h1 := T_le_NS hS'
  have h2 := card_le_AS hS hw
  have hd := NS_decomp (G := G) S w
  rw [Finset.card_erase_of_mem hw] at h1
  have hs : #S = (#S - 1) + 1 := (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 ⟨w, hw⟩)).symm
  rw [hs, T_succ] at ht
  omega

omit [DecidablePred (Sep G)] in
/-- Every connected set with at least two elements has a vertex whose removal leaves a connected
set. -/
theorem exists_noncut {S : Finset V} (hS : Sep G S) (h2 : 2 ≤ #S) :
    ∃ w ∈ S, Sep G (S.erase w) := by
  obtain ⟨r, hr⟩ := hS.1
  obtain ⟨P, hPS, hP, -, hPc⟩ := exists_sep_card hS hr (#S - 1) (by omega) (by omega)
  obtain ⟨w, hwS, hwP⟩ : ∃ w ∈ S, w ∉ P := by
    by_contra hcon
    push Not at hcon
    have := Finset.card_le_card (show S ⊆ P from hcon)
    omega
  refine ⟨w, hwS, ?_⟩
  have : P = S.erase w := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      exact Finset.mem_erase.2 ⟨fun h => hwP (h ▸ hx), hPS hx⟩
    · rw [Finset.card_erase_of_mem hwS, hPc]
  rw [← this]; exact hP

/-! ### The enumeration given by an end -/

/-- An end `y` of a connected set `S` gives an enumeration `φ 0 = y, …, φ (#S-1)` of `S` in which
consecutive vertices are adjacent. -/
theorem chain_of_end : ∀ s (S : Finset V) (y : V), Sep G S → y ∈ S → #S = s → AS G S y = s →
    ∃ φ : ℕ → V, φ 0 = y ∧ (∀ i < s, φ i ∈ S) ∧ (∀ i < s, ∀ j < s, φ i = φ j → i = j) ∧
      (∀ v ∈ S, ∃ i < s, φ i = v) ∧ (∀ i, i + 1 < s → G.Adj (φ i) (φ (i + 1))) := by
  intro s
  induction s with
  | zero => intro S y _ hy hs _; exact absurd hs (Finset.card_ne_zero.2 ⟨y, hy⟩)
  | succ s ih =>
    intro S y hS hy hs hA
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 hs
      rw [Finset.mem_singleton] at hy
      subst hy
      refine ⟨fun _ => y, rfl, fun _ _ => Finset.mem_singleton_self y, ?_, ?_, ?_⟩
      · intro i hi j hj _; omega
      · intro v hv; exact ⟨0, by omega, (Finset.mem_singleton.1 hv).symm⟩
      · intro i hi; omega
    have hne : ({y} : Finset V) ≠ S := by
      intro h; rw [← h, Finset.card_singleton] at hs; omega
    obtain ⟨a, ha, b, hbS, hby, hab⟩ :=
      hS.2 {y} (Finset.singleton_subset_iff.2 hy) (Finset.singleton_nonempty y) hne
    rw [Finset.mem_singleton] at ha
    subst ha
    rw [Finset.mem_singleton] at hby
    have huniq : ∀ z ∈ S, G.Adj a z → z = b := by
      intro z hz hza
      by_contra hzb
      have := succ_le_AS_of_two hS hy hbS hz (Ne.symm hzb) hab hza
      omega
    obtain ⟨hS', hA'⟩ := AS_pendant hS hy hbS hab huniq
    have hcard : #(S.erase a) = s := by rw [Finset.card_erase_of_mem hy, hs]; rfl
    have hb' : b ∈ S.erase a := Finset.mem_erase.2 ⟨hby, hbS⟩
    obtain ⟨ψ, hψ0, hψS, hψinj, hψsurj, hψadj⟩ := ih (S.erase a) b hS' hb' hcard (by omega)
    let φ : ℕ → V := fun i => Nat.casesOn i a ψ
    have hφ0 : φ 0 = a := rfl
    have hφs : ∀ i, φ (i + 1) = ψ i := fun _ => rfl
    have hψa : ∀ i < s, ψ i ≠ a := fun i hi h => by
      have := hψS i hi; rw [h] at this; simp at this
    refine ⟨φ, rfl, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rcases i with _ | i
      · exact hy
      · rw [hφs]; exact Finset.mem_of_mem_erase (hψS i (by omega))
    · intro i hi j hj hij
      rcases i with _ | i <;> rcases j with _ | j
      · rfl
      · rw [hφ0, hφs] at hij; exact absurd hij.symm (hψa j (by omega))
      · rw [hφ0, hφs] at hij; exact absurd hij (hψa i (by omega))
      · rw [hφs, hφs] at hij; rw [hψinj i (by omega) j (by omega) hij]
    · intro v hv
      by_cases hva : v = a
      · exact ⟨0, by omega, hva.symm⟩
      · obtain ⟨i, hi, hiv⟩ := hψsurj v (Finset.mem_erase.2 ⟨hva, hv⟩)
        exact ⟨i + 1, by omega, hiv⟩
    · intro i hi
      rcases i with _ | i
      · rw [hφ0, hφs, hψ0]; exact hab
      · rw [hφs, hφs]; exact hψadj i (by omega)

/-! ### Intervals of an enumeration -/

section intervals

variable {s : ℕ} {φ : ℕ → V}

/-- The interval `{φ a, …, φ b}`. -/
def Ivl (φ : ℕ → V) (a b : ℕ) : Finset V := (Finset.Icc a b).image φ

omit [DecidablePred (Sep G)] in
theorem sep_Ivl (hadj : ∀ i, i + 1 < s → G.Adj (φ i) (φ (i + 1)))
    (hinj : ∀ i < s, ∀ j < s, φ i = φ j → i = j) {a : ℕ} :
    ∀ b, a ≤ b → b < s → Sep G (Ivl φ a b) := by
  intro b hab hbs
  induction b, hab using Nat.le_induction with
  | base => simpa [Ivl] using sep_singleton G (φ a)
  | succ b hab ih =>
    have heq : Ivl φ a (b + 1) = insert (φ (b + 1)) (Ivl φ a b) := by
      unfold Ivl
      have hI : Finset.Icc a (b + 1) = insert (b + 1) (Finset.Icc a b) := by
        ext x; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
      rw [hI, Finset.image_insert]
    rw [heq]
    refine sep_insert (ih (by omega)) ?_ ⟨φ b, ?_, hadj b hbs⟩
    · intro h
      simp only [Ivl, Finset.mem_image, Finset.mem_Icc] at h
      obtain ⟨i, hi, hiφ⟩ := h
      have := hinj i (by omega) (b + 1) hbs hiφ
      omega
    · simp only [Ivl, Finset.mem_image, Finset.mem_Icc]
      exact ⟨b, ⟨hab, le_rfl⟩, rfl⟩

omit [DecidablePred (Sep G)] in
theorem mem_Ivl_iff (hinj : ∀ i < s, ∀ j < s, φ i = φ j → i = j) {a b i : ℕ} (hb : b < s)
    (hi : i < s) : φ i ∈ Ivl φ a b ↔ a ≤ i ∧ i ≤ b := by
  simp only [Ivl, Finset.mem_image, Finset.mem_Icc]
  constructor
  · rintro ⟨j, hj, hji⟩
    have := hinj j (by omega) i hi hji
    subst this; exact hj
  · intro h; exact ⟨i, h, rfl⟩

omit [DecidablePred (Sep G)] in
theorem Ivl_subset (hS : ∀ i < s, φ i ∈ S) {a b : ℕ} (hb : b < s) : Ivl φ a b ⊆ S := by
  intro v hv
  simp only [Ivl, Finset.mem_image, Finset.mem_Icc] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  exact hS i (by omega)

omit [DecidablePred (Sep G)] in
theorem Ivl_inj (hinj : ∀ i < s, ∀ j < s, φ i = φ j → i = j) {a b a' b' : ℕ} (hab : a ≤ b)
    (hab' : a' ≤ b') (hb : b < s) (hb' : b' < s) (h : Ivl φ a b = Ivl φ a' b') :
    a = a' ∧ b = b' := by
  have h1 := (mem_Ivl_iff hinj hb' (by omega : a < s)).1 (h ▸ (mem_Ivl_iff hinj hb (by omega)).2
    ⟨le_rfl, hab⟩)
  have h2 := (mem_Ivl_iff hinj hb' hb).1 (h ▸ (mem_Ivl_iff hinj hb hb).2 ⟨hab, le_rfl⟩)
  have h3 := (mem_Ivl_iff hinj hb (by omega : a' < s)).1 (h.symm ▸ (mem_Ivl_iff hinj hb'
    (by omega)).2 ⟨le_rfl, hab'⟩)
  have h4 := (mem_Ivl_iff hinj hb hb').1 (h.symm ▸ (mem_Ivl_iff hinj hb' hb').2 ⟨hab', le_rfl⟩)
  omega

end intervals

/-! ### Attaching a vertex -/

theorem two_mul_le_aux (i m : ℕ) (h1 : 1 ≤ i) (h2 : i + 2 ≤ m) :
    2 * (m - 1) ≤ (i + 1) * (m - i) := by
  obtain ⟨p, rfl⟩ : ∃ p, i = p + 1 := ⟨i - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, m = p + 3 + q := ⟨m - (p + 3), by omega⟩
  have e1 : p + 3 + q - 1 = p + q + 2 := by omega
  have e2 : p + 3 + q - (p + 1) = q + 2 := by omega
  rw [e1, e2]
  nlinarith

/-- Let `S` be connected, `w ∈ S`, and suppose that `S.erase w` is connected with the minimum
number `T (#S - 1)` of connected subsets, while `S` does not have the minimum `T #S`. Then `w` lies
in at least `2 #S - 3` connected subsets of `S`. -/
theorem attach_bound {S : Finset V} {w : V} (hS : Sep G S) (hw : w ∈ S)
    (hH : Sep G (S.erase w)) (htH : NS G (S.erase w) = T (#S - 1)) (hnt : NS G S ≠ T #S)
    (h3 : 3 ≤ #S) : 2 * #S - 3 ≤ AS G S w := by
  set H := S.erase w with hHdef
  set m := #S - 1 with hm
  have hHc : #H = m := by rw [hHdef, Finset.card_erase_of_mem hw]
  obtain ⟨y, hyH, hHy⟩ := exists_noncut hH (by omega)
  have hAy : AS G H y = m := by rw [← hHc]; exact end_of_tight hH hyH hHy (by rw [hHc, htH])
  obtain ⟨φ, -, hφS, hφinj, hφsurj, hφadj⟩ := chain_of_end m H y hH hyH hHc hAy
  have hwH : w ∉ H := by simp [hHdef]
  set F := {X ∈ S.powerset | Sep G X ∧ w ∈ X} with hF
  have hAF : AS G S w = #F := rfl
  have hmemF : ∀ a b i, a ≤ i → i ≤ b → b < m → G.Adj w (φ i) → insert w (Ivl φ a b) ∈ F := by
    intro a b i hai hib hbm hwi
    have hsub : Ivl φ a b ⊆ H := Ivl_subset hφS hbm
    simp only [hF, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hw (hsub.trans (Finset.erase_subset _ _)), ?_,
      Finset.mem_insert_self _ _⟩
    refine sep_insert (sep_Ivl hφadj hφinj b (by omega) hbm) (fun h => hwH (hsub h))
      ⟨φ i, ?_, hwi.symm⟩
    exact (mem_Ivl_iff hφinj hbm (by omega)).2 ⟨hai, hib⟩
  have hsingF : {w} ∈ F := by simp [hF, hw, sep_singleton]
  have hinsinj : ∀ a b a' b', a ≤ b → a' ≤ b' → b < m → b' < m →
      insert w (Ivl φ a b) = insert w (Ivl φ a' b') → a = a' ∧ b = b' := by
    intro a b a' b' hab hab' hb hb' h
    apply Ivl_inj hφinj hab hab' hb hb'
    have hw1 : w ∉ Ivl φ a b := fun h' => hwH (Ivl_subset hφS hb h')
    have hw2 : w ∉ Ivl φ a' b' := fun h' => hwH (Ivl_subset hφS hb' h')
    rw [← Finset.erase_insert hw1, h, Finset.erase_insert hw2]
  have hne_sing : ∀ a b, a ≤ b → b < m → insert w (Ivl φ a b) ≠ {w} := by
    intro a b hab hb h
    have : φ a ∈ ({w} : Finset V) := by
      rw [← h]; exact Finset.mem_insert_of_mem ((mem_Ivl_iff hφinj hb (by omega)).2 ⟨le_rfl, hab⟩)
    rw [Finset.mem_singleton] at this
    exact hwH (this ▸ hφS a (by omega))
  have hφH : ∀ i < m, φ i ≠ w := fun i hi h => hwH (h ▸ hφS i hi)
  by_cases hA : ∃ i, 1 ≤ i ∧ i + 2 ≤ m ∧ G.Adj w (φ i)
  · -- `w` is adjacent to an inner vertex `φ i`
    obtain ⟨i, hi1, hi2, hwi⟩ := hA
    set P := Finset.Icc 0 i ×ˢ Finset.Icc i (m - 1) with hP
    have hPc : #P = (i + 1) * (m - i) := by
      rw [hP, Finset.card_product, Nat.card_Icc, Nat.card_Icc]; congr 1; omega
    set Fam := P.image (fun p => insert w (Ivl φ p.1 p.2)) with hFam
    have hFamc : #Fam = #P := by
      apply Finset.card_image_of_injOn
      intro p hp q hq h
      simp only [hP, Finset.coe_product, Set.mem_prod, Finset.coe_Icc, Set.mem_Icc] at hp hq
      obtain ⟨h1, h2⟩ := hinsinj p.1 p.2 q.1 q.2 (by omega) (by omega) (by omega) (by omega) h
      exact Prod.ext h1 h2
    have hsub : insert {w} Fam ⊆ F := by
      intro X hX
      rcases Finset.mem_insert.1 hX with rfl | hX
      · exact hsingF
      · simp only [hFam, Finset.mem_image, hP, Finset.mem_product, Finset.mem_Icc] at hX
        obtain ⟨p, hp, rfl⟩ := hX
        exact hmemF p.1 p.2 i (by omega) (by omega) (by omega) hwi
    have hnotin : {w} ∉ Fam := by
      intro h
      simp only [hFam, Finset.mem_image, hP, Finset.mem_product, Finset.mem_Icc] at h
      obtain ⟨p, hp, hpw⟩ := h
      exact hne_sing p.1 p.2 (by omega) (by omega) hpw
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnotin, hFamc, hPc] at h1
    have h2 := two_mul_le_aux i m hi1 hi2
    rw [hAF]; omega
  by_cases hB : G.Adj w (φ 0) ∧ G.Adj w (φ (m - 1))
  · -- `w` is adjacent to both ends
    obtain ⟨hw0, hwm⟩ := hB
    set Fam1 := (Finset.range m).image (fun b => insert w (Ivl φ 0 b)) with hFam1
    set Fam2 := (Finset.Icc 1 (m - 1)).image (fun a => insert w (Ivl φ a (m - 1))) with hFam2
    have hc1 : #Fam1 = m := by
      rw [hFam1, Finset.card_image_of_injOn, Finset.card_range]
      intro b hb b' hb' h
      simp only [Finset.coe_range, Set.mem_Iio] at hb hb'
      exact (hinsinj 0 b 0 b' (by omega) (by omega) hb hb' h).2
    have hc2 : #Fam2 = m - 1 := by
      rw [hFam2, Finset.card_image_of_injOn, Nat.card_Icc]
      · omega
      intro a ha a' ha' h
      simp only [Finset.coe_Icc, Set.mem_Icc] at ha ha'
      exact (hinsinj a (m - 1) a' (m - 1) (by omega) (by omega) (by omega) (by omega) h).1
    have hdisj : Disjoint Fam1 Fam2 := by
      rw [Finset.disjoint_left]
      intro X h1 h2
      simp only [hFam1, hFam2, Finset.mem_image, Finset.mem_range, Finset.mem_Icc] at h1 h2
      obtain ⟨b, hb, rfl⟩ := h1
      obtain ⟨a, ha, hX⟩ := h2
      have : φ 0 ∈ insert w (Ivl φ a (m - 1)) := by
        rw [hX]; exact Finset.mem_insert_of_mem ((mem_Ivl_iff hφinj hb (by omega)).2 ⟨le_rfl, by omega⟩)
      rcases Finset.mem_insert.1 this with h | h
      · exact hφH 0 (by omega) h
      · have := (mem_Ivl_iff hφinj (by omega) (by omega)).1 h; omega
    have hsub : insert {w} (Fam1 ∪ Fam2) ⊆ F := by
      intro X hX
      rcases Finset.mem_insert.1 hX with rfl | hX
      · exact hsingF
      rcases Finset.mem_union.1 hX with hX | hX
      · simp only [hFam1, Finset.mem_image, Finset.mem_range] at hX
        obtain ⟨b, hb, rfl⟩ := hX
        exact hmemF 0 b 0 le_rfl (by omega) hb hw0
      · simp only [hFam2, Finset.mem_image, Finset.mem_Icc] at hX
        obtain ⟨a, ha, rfl⟩ := hX
        exact hmemF a (m - 1) (m - 1) (by omega) le_rfl (by omega) hwm
    have hnotin : {w} ∉ Fam1 ∪ Fam2 := by
      intro h
      rcases Finset.mem_union.1 h with h | h
      · simp only [hFam1, Finset.mem_image, Finset.mem_range] at h
        obtain ⟨b, hb, hbw⟩ := h
        exact hne_sing 0 b (by omega) hb hbw
      · simp only [hFam2, Finset.mem_image, Finset.mem_Icc] at h
        obtain ⟨a, ha, haw⟩ := h
        exact hne_sing a (m - 1) (by omega) (by omega) haw
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hnotin, Finset.card_union_of_disjoint hdisj, hc1, hc2] at h1
    rw [hAF]; omega
  · -- `w` has a unique neighbour, an end of `H`; then `S` would have the minimum
    exfalso
    have hnb : ∀ z ∈ S, G.Adj w z → z = φ 0 ∨ z = φ (m - 1) := by
      intro z hz hwz
      have hzH : z ∈ H := Finset.mem_erase.2 ⟨(G.ne_of_adj hwz).symm, hz⟩
      obtain ⟨i, hi, rfl⟩ := hφsurj z hzH
      by_cases hi0 : i = 0
      · left; rw [hi0]
      by_cases him : i = m - 1
      · right; rw [him]
      exact absurd ⟨i, by omega, by omega, hwz⟩ hA
    have hne : ({w} : Finset V) ≠ S := by
      intro h; rw [← h, Finset.card_singleton] at h3; omega
    obtain ⟨a, ha, x, hxS, hxw, hax⟩ :=
      hS.2 {w} (Finset.singleton_subset_iff.2 hw) (Finset.singleton_nonempty w) hne
    rw [Finset.mem_singleton] at ha
    subst ha
    have huniq : ∀ z ∈ S, G.Adj a z → z = x := by
      intro z hz haz
      by_contra hzx
      apply hB
      rcases hnb z hz haz with h1 | h1 <;> rcases hnb x hxS hax with h2 | h2
      · exact absurd (h1.trans h2.symm) hzx
      · exact ⟨h1 ▸ haz, h2 ▸ hax⟩
      · exact ⟨h2 ▸ hax, h1 ▸ haz⟩
      · exact absurd (h1.trans h2.symm) hzx
    have hxH : x ∈ H := Finset.mem_erase.2 ⟨(G.ne_of_adj hax).symm, hxS⟩
    -- `x` is a vertex whose removal leaves `H` connected
    have hHx : Sep G (H.erase x) := by
      rcases hnb x hxS hax with hx | hx
      · have : H.erase x = Ivl φ 1 (m - 1) := by
          ext v
          constructor
          · intro hv
            obtain ⟨hvx, hvH⟩ := Finset.mem_erase.1 hv
            obtain ⟨i, hi, rfl⟩ := hφsurj v hvH
            have hi0 : i ≠ 0 := fun h => hvx (by rw [h, hx])
            exact (mem_Ivl_iff hφinj (by omega) hi).2 ⟨by omega, by omega⟩
          · intro hv
            simp only [Ivl, Finset.mem_image, Finset.mem_Icc] at hv
            obtain ⟨i, hi, rfl⟩ := hv
            refine Finset.mem_erase.2 ⟨fun h => ?_, hφS i (by omega)⟩
            rw [hx] at h
            have := hφinj i (by omega) 0 (by omega) h
            omega
        rw [this]; exact sep_Ivl hφadj hφinj (m - 1) (by omega) (by omega)
      · have : H.erase x = Ivl φ 0 (m - 2) := by
          ext v
          constructor
          · intro hv
            obtain ⟨hvx, hvH⟩ := Finset.mem_erase.1 hv
            obtain ⟨i, hi, rfl⟩ := hφsurj v hvH
            have him : i ≠ m - 1 := fun h => hvx (by rw [h, hx])
            exact (mem_Ivl_iff hφinj (by omega) hi).2 ⟨by omega, by omega⟩
          · intro hv
            simp only [Ivl, Finset.mem_image, Finset.mem_Icc] at hv
            obtain ⟨i, hi, rfl⟩ := hv
            refine Finset.mem_erase.2 ⟨fun h => ?_, hφS i (by omega)⟩
            rw [hx] at h
            have := hφinj i (by omega) (m - 1) (by omega) h
            omega
        rw [this]; exact sep_Ivl hφadj hφinj (m - 2) (by omega) (by omega)
    have hAx : AS G H x = m := by
      rw [← hHc]; exact end_of_tight hH hxH hHx (by rw [hHc, htH])
    obtain ⟨-, hAw⟩ := AS_pendant hS hw hxS hax huniq
    have hend : AS G S a = #S := by rw [hAw, hAx]; omega
    exact hnt (NS_eq_T_of_end #S S a hS hw rfl hend)

/-! ### The dichotomy -/

/-- **The gap above the path.** A connected set `S` with `s` elements has either exactly `T s`
connected subsets, or at least `T s + (s - 3)`. -/
theorem NS_gap : ∀ s (S : Finset V), Sep G S → #S = s → NS G S = T s ∨ T s + (s - 3) ≤ NS G S := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro S hS hs
  by_cases ht : NS G S = T s
  · exact Or.inl ht
  right
  have hT := T_le_NS hS
  rw [hs] at hT
  by_cases hs4 : s ≤ 4
  · omega
  push Not at hs4
  obtain ⟨w, hw, hH⟩ := exists_noncut hS (by omega)
  have hHc : #(S.erase w) = s - 1 := by rw [Finset.card_erase_of_mem hw, hs]
  have hd := NS_decomp (G := G) S w
  have hsT : T s = T (s - 1) + s := by
    have e : s = (s - 1) + 1 := by omega
    conv_lhs => rw [e]
    rw [T_succ, ← e]
  rcases ih (s - 1) (by omega) (S.erase w) hH hHc with hH' | hH'
  · have := attach_bound hS hw hH (by rw [hH', hs]) (by rw [hs]; exact ht) (by omega)
    rw [hs] at this
    omega
  · have h1 := card_le_AS hS hw
    rw [hs] at h1
    have h2 : AS G S w ≠ s := fun h => ht (NS_eq_T_of_end s S w hS hw hs h)
    omega

end ConnectedSets
