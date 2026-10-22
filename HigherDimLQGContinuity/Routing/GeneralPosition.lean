import HigherDimLQGContinuity.Routing.Grid

/-!
# Rational general position (`d ≥ 3`)

Packet Q2 (ruling N9). Sources: planning audit `planning/audits/NA2-section-4.md`, §1.5 and
Details (c) **R4**; blueprint Part B, Lemma `b:lem-gp` ([C] p. 11–12, l. 579–594).

**Statement** (`rational_general_position`, explicit form `rational_general_position_explicit`).
Free vertices of a configuration `v : Fin n → ℝ^d` (fixed vertices distinct and on the grid
`o + νℤ^d`, every edge with a free endpoint) can be moved by at most `δ` onto the grid so that
the vertices are distinct, incident edges meet only at their common vertex (and their three
endpoints are not collinear), and edges without a common vertex are at distance
`≥ ν³/(2R₀ + 2)²`, provided `ν ≤ c₀ δ/(n + 1)³`, `c₀ = 3^{-d} d^{-d/2}` (`gpC0`).

**Proof.** The core (`gp_core`, any finite index type) keeps the invariant `GPInv`: every set `S`
of at most four determined indices with at most two fixed ones is affinely independent (weight
form `WIndep`). Free vertices are added one at a time (`Finset.induction_on`); the new vertex `X` is
a grid point within `√d ν (n³ + 1)` of `v X` avoiding the affine planes `w Y + span(w Z - w Y,
w W - w Y)` of all `n³` triples (`exists_onGrid_avoid`), and `gpInv_insert` shows the invariant
persists: if a vanishing weighted sum over `S ∋ X` gave `X` a nonzero weight, `w X - w Y` would
be a combination of at most two vectors `w Z - w Y`. The fixed vertices alone are distinct
(`gpInv_base`). The separations follow from `grid_segment_sep` and `segment_inter_segment_eq`.
Compared with the blueprint, all `n³` triples are excluded (not only lines and the planes of edge
pairs); the count `n³ < n³ + 1` grid points per coordinate is what `ν ≤ c₀δ/(n + 1)³` pays for.

**Correction of the NA2 probe shape.** With ordered edges `E : Finset (Fin n × Fin n)` the probe's
incident clause (`e ≠ e' → e.2 = e'.1 → [w e.1, w e.2] ∩ [w e'.1, w e'.2] = {w e.2}`) is false for
the reversed pair `e = (0, 1)`, `e' = (1, 0)`: it forces `w 0 = w 1`, impossible when
`|v 0 - v 1| > 2δ`. The blueprint's unordered edges (used here, `Sym2`) avoid this; the incident
clause is stated for `s(i, j), s(j, k) ∈ E` with `i ≠ k`. The minimally corrected ordered form
(extra hypothesis `e.1 ≠ e'.2` in the incident clause) is `rational_general_position_ordered`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open scoped InnerProductSpace

namespace HigherDimLQGContinuity.Routing

variable {d : ℕ}

/-! ### The invariant -/

section Invariant

variable {ι : Type*} [DecidableEq ι]

/-- A set of at most four indices with at most two fixed ones. -/
def GPGood (F S : Finset ι) : Prop :=
  S.card ≤ 4 ∧ S.card ≤ (S.filter (· ∉ F)).card + 2

/-- The points `w i`, `i ∈ S`, are affinely independent (weight form). -/
def WIndep (w : ι → Rd d) (S : Finset ι) : Prop :=
  ∀ lam : ι → ℝ, ∑ i ∈ S, lam i = 0 → ∑ i ∈ S, lam i • w i = 0 → ∀ i ∈ S, lam i = 0

/-- The invariant of the construction: good subsets of `D` are affinely independent. -/
def GPInv (F : Finset ι) (w : ι → Rd d) (D : Finset ι) : Prop :=
  ∀ S ⊆ D, GPGood F S → WIndep w S

omit [DecidableEq ι] in
lemma wIndep_congr {w w' : ι → Rd d} {S : Finset ι} (h : ∀ i ∈ S, w i = w' i)
    (hw : WIndep w S) : WIndep w' S := by
  intro lam h1 h2
  refine hw lam h1 ?_
  rw [← h2]
  exact Finset.sum_congr rfl fun i hi => by rw [h i hi]

lemma gpInv_congr {F D : Finset ι} {w w' : ι → Rd d} (h : ∀ i ∈ D, w i = w' i)
    (hw : GPInv F w D) : GPInv F w' D :=
  fun S hS hG => wIndep_congr (fun i hi => h i (hS hi)) (hw S hS hG)

/-- **Base**: distinct fixed points; good subsets of `F` have at most two elements. -/
lemma gpInv_base {F : Finset ι} {w : ι → Rd d} (hinj : Set.InjOn w F) : GPInv F w F := by
  intro S hS hG lam h1 h2
  have hf : S.filter (· ∉ F) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i hi hiF
    exact hiF (hS hi)
  have hc : S.card ≤ 2 := by
    have := hG.2
    rw [hf, Finset.card_empty] at this
    omega
  rcases (by omega : S.card = 0 ∨ S.card = 1 ∨ S.card = 2) with h0 | h0 | h0
  · rw [Finset.card_eq_zero] at h0
    subst h0
    intro i hi
    exact absurd hi (Finset.notMem_empty i)
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h0
    rw [Finset.sum_singleton] at h1
    intro i hi
    rw [Finset.mem_singleton.1 hi]
    exact h1
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.1 h0
    rw [Finset.sum_pair hab] at h1 h2
    have hb : lam b = -lam a := by linarith
    rw [hb, neg_smul, ← sub_eq_add_neg, ← smul_sub] at h2
    have hne : w a - w b ≠ 0 := by
      rw [sub_ne_zero]
      exact fun h => hab (hinj (hS (Finset.mem_insert_self a {b}))
        (hS (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))) h)
    have ha : lam a = 0 := (smul_eq_zero.1 h2).resolve_right hne
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ha
    · rw [Finset.mem_singleton.1 hi, hb, ha, neg_zero]

/-- A combination of at most two differences `w i - w Y` with `i ∈ T` is a combination of two such
differences with indices in `insert Y T`. -/
lemma exists_pair_combination (w : ι → Rd d) (Y : ι) (T : Finset ι) (μ : ι → ℝ)
    (hT : T.card ≤ 2) :
    ∃ Z ∈ insert Y T, ∃ W ∈ insert Y T, ∃ b c : ℝ,
      ∑ i ∈ T, μ i • (w i - w Y) = b • (w Z - w Y) + c • (w W - w Y) := by
  rcases (by omega : T.card = 0 ∨ T.card = 1 ∨ T.card = 2) with h0 | h0 | h0
  · rw [Finset.card_eq_zero] at h0
    subst h0
    exact ⟨Y, Finset.mem_insert_self _ _, Y, Finset.mem_insert_self _ _, 0, 0, by simp⟩
  · obtain ⟨Z, rfl⟩ := Finset.card_eq_one.1 h0
    refine ⟨Z, Finset.mem_insert_of_mem (Finset.mem_singleton_self Z), Y,
      Finset.mem_insert_self _ _, μ Z, 0, ?_⟩
    simp
  · obtain ⟨Z, W, hZW, rfl⟩ := Finset.card_eq_two.1 h0
    refine ⟨Z, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), W,
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)), μ Z, μ W,
      ?_⟩
    rw [Finset.sum_pair hZW]

/-- **Insertion**: a free index `X` whose point avoids the affine planes of all triples of `D`
preserves the invariant. -/
lemma gpInv_insert {F D : Finset ι} {w : ι → Rd d} {X : ι} (hXD : X ∉ D) (hXF : X ∉ F)
    (hD : GPInv F w D)
    (havoid : ∀ Y ∈ D, ∀ Z ∈ D, ∀ W ∈ D, ∀ b c : ℝ,
      w X - w Y ≠ b • (w Z - w Y) + c • (w W - w Y)) :
    GPInv F w (insert X D) := by
  intro S hS hG
  by_cases hXS : X ∉ S
  · have hSD : S ⊆ D := fun i hi => by
      rcases Finset.mem_insert.1 (hS hi) with rfl | h
      · exact absurd hi hXS
      · exact h
    exact hD S hSD hG
  push Not at hXS
  set S' := S.erase X with hS'
  have hS'D : S' ⊆ D := fun i hi => by
    rcases Finset.mem_insert.1 (hS (Finset.mem_of_mem_erase hi)) with rfl | h
    · exact absurd rfl (Finset.ne_of_mem_erase hi)
    · exact h
  have hcard : S'.card + 1 = S.card := Finset.card_erase_add_one hXS
  have hfilt : (S'.filter (· ∉ F)).card + 1 = (S.filter (· ∉ F)).card := by
    rw [hS', Finset.filter_erase]
    exact Finset.card_erase_add_one (Finset.mem_filter.2 ⟨hXS, hXF⟩)
  have hG' : GPGood F S' := ⟨by have := hG.1; omega, by have := hG.2; omega⟩
  intro lam h1 h2
  rw [← Finset.add_sum_erase S _ hXS] at h1 h2
  rw [← hS'] at h1 h2
  -- the weight of `X` vanishes
  have hX : lam X = 0 := by
    by_contra hX0
    have hne : S'.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [h, Finset.sum_empty, add_zero] at h1
      exact hX0 h1
    obtain ⟨Y, hY⟩ := hne
    have hsumY : ∑ i ∈ S', lam i • (w i - w Y) = -lam X • (w X - w Y) := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
      have e1 : ∑ i ∈ S', lam i = -lam X := by linarith
      have e2 : ∑ i ∈ S', lam i • w i = -(lam X • w X) := eq_neg_of_add_eq_zero_right h2
      rw [e1, e2]
      module
    set T := S'.erase Y with hT
    have hTc : T.card ≤ 2 := by
      have h' : T.card + 1 = S'.card := Finset.card_erase_add_one hY
      have := hG.1
      omega
    rw [← Finset.add_sum_erase S' _ hY, sub_self, smul_zero, zero_add, ← hT] at hsumY
    obtain ⟨Z, hZ, W, hW, b, c, hbc⟩ :=
      exists_pair_combination w Y T (fun i => -(lam X)⁻¹ * lam i) hTc
    have hYT : insert Y T ⊆ D := by
      rw [hT, Finset.insert_erase hY]
      exact hS'D
    apply havoid Y (hS'D hY) Z (hYT hZ) W (hYT hW) b c
    rw [← hbc]
    simp_rw [mul_smul]
    rw [← Finset.smul_sum, hsumY, smul_smul, neg_mul_neg, inv_mul_cancel₀ hX0, one_smul]
  rw [hX, zero_smul, zero_add] at h2
  rw [hX, zero_add] at h1
  have hrest := hD S' hS'D hG' lam h1 h2
  intro i hi
  by_cases hiX : i = X
  · rw [hiX]; exact hX
  · exact hrest i (Finset.mem_erase.2 ⟨hiX, hi⟩)

end Invariant

/-! ### The construction -/

/-- **Core of rational general position** (any finite index type): free vertices move by at most
`δ` onto the grid so that every set of at most four indices with at most two fixed ones is affinely
independent, provided `√d ν (n³ + 1) ≤ δ`, `n = #ι`. -/
theorem gp_core (hd : 3 ≤ d) {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → Rd d)
    (F : Finset ι) {ν δ : ℝ} (o : Rd d) (hν : 0 < ν)
    (hνδ : √(d : ℝ) * ν * ((Fintype.card ι : ℝ) ^ 3 + 1) ≤ δ)
    (hF : ∀ i ∈ F, OnGrid ν o (v i)) (hinj : Set.InjOn v F) :
    ∃ w : ι → Rd d, (∀ i ∈ F, w i = v i) ∧ (∀ i, ‖w i - v i‖ ≤ δ) ∧
      (∀ i, OnGrid ν o (w i)) ∧ GPInv F w Finset.univ := by
  have hδ0 : 0 ≤ δ := le_trans (by positivity) hνδ
  -- the induction over the processed free indices
  have key : ∀ T : Finset ι, (∀ i ∈ T, i ∉ F) → ∃ w : ι → Rd d, (∀ i ∈ F, w i = v i) ∧
      (∀ i ∈ T, ‖w i - v i‖ ≤ δ ∧ OnGrid ν o (w i)) ∧ GPInv F w (F ∪ T) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      refine ⟨v, fun _ _ => rfl, fun i hi => absurd hi (Finset.notMem_empty i), ?_⟩
      rw [Finset.union_empty]
      exact gpInv_base hinj
    | insert X T hXT ih =>
      intro hT
      obtain ⟨w, hwF, hwT, hwI⟩ := ih fun i hi => hT i (Finset.mem_insert_of_mem hi)
      have hXF : X ∉ F := hT X (Finset.mem_insert_self _ _)
      obtain ⟨x, hxg, hxv, hxa⟩ := exists_onGrid_avoid hd hν o (v X) (T := ι × ι × ι)
        (fun τ => w τ.1) (fun τ => w τ.2.1) (fun τ => w τ.2.2)
        (M := Fintype.card ι ^ 3 + 1)
        (by rw [Fintype.card_prod, Fintype.card_prod]; nlinarith)
      set w' := Function.update w X x with hw'
      have hw'X : w' X = x := Function.update_self X x w
      have hw'o : ∀ i, i ≠ X → w' i = w i := fun i hi => Function.update_of_ne hi x w
      have hXD : X ∉ F ∪ T := by
        rw [Finset.mem_union, not_or]; exact ⟨hXF, hXT⟩
      refine ⟨w', fun i hi => ?_, fun i hi => ?_, ?_⟩
      · rw [hw'o i (fun h => hXF (h ▸ hi))]; exact hwF i hi
      · rcases Finset.mem_insert.1 hi with rfl | hi
        · refine ⟨?_, hw'X ▸ hxg⟩
          rw [hw'X]
          refine hxv.trans (le_of_eq_of_le ?_ hνδ)
          push_cast
          ring
        · rw [hw'o i (fun h => hXT (h ▸ hi))]; exact hwT i hi
      · have hI' : GPInv F w' (F ∪ T) :=
          gpInv_congr (fun i hi => (hw'o i (fun h => hXD (h ▸ hi))).symm) hwI
        have hunion : F ∪ insert X T = insert X (F ∪ T) := by
          rw [Finset.union_insert]
        rw [hunion]
        refine gpInv_insert hXD hXF hI' fun Y hY Z hZ W hW b c => ?_
        rw [hw'X, hw'o Y (fun h => hXD (h ▸ hY)), hw'o Z (fun h => hXD (h ▸ hZ)),
          hw'o W (fun h => hXD (h ▸ hW))]
        exact hxa (Y, Z, W) b c
  classical
  obtain ⟨w, hwF, hwT, hwI⟩ := key (Finset.univ \ F) fun i hi => (Finset.mem_sdiff.1 hi).2
  refine ⟨w, hwF, fun i => ?_, fun i => ?_, ?_⟩
  · by_cases hi : i ∈ F
    · rw [hwF i hi, sub_self, norm_zero]; exact hδ0
    · exact (hwT i (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hi⟩)).1
  · by_cases hi : i ∈ F
    · rw [hwF i hi]; exact hF i hi
    · exact (hwT i (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hi⟩)).2
  · rwa [Finset.union_sdiff_of_subset (Finset.subset_univ F)] at hwI

/-! ### Consequences of the invariant -/

section Consequences

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Finset ι} {w : ι → Rd d}

/-- The construction gives distinct points. -/
lemma GPInv.injective (h : GPInv F w Finset.univ) : Function.Injective w := by
  intro i j hij
  by_contra hne
  have hG : GPGood F {i, j} := by
    unfold GPGood
    rw [Finset.card_pair hne]
    exact ⟨by norm_num, by omega⟩
  have := h {i, j} (Finset.subset_univ _) hG (fun k => if k = i then 1 else -1)
    (by rw [Finset.sum_pair hne]; simp [Ne.symm hne])
    (by rw [Finset.sum_pair hne]; simp [Ne.symm hne, hij])
    i (Finset.mem_insert_self _ _)
  simp at this

/-- Three distinct indices, not all fixed: affinely independent (weight form). -/
lemma GPInv.indep3 (h : GPInv F w Finset.univ) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hfree : i ∉ F ∨ j ∉ F ∨ k ∉ F) :
    ∀ a b c : ℝ, a + b + c = 0 → a • w i + b • w j + c • w k = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  intro a b c habc hcomb
  have hjk' : j ∉ ({k} : Finset ι) := by simpa using hjk
  have hi' : i ∉ ({j, k} : Finset ι) := by simp [hij, hik]
  have hcard : ({i, j, k} : Finset ι).card = 3 := by
    rw [Finset.card_insert_of_notMem hi', Finset.card_pair hjk]
  have hfc : 1 ≤ (({i, j, k} : Finset ι).filter (· ∉ F)).card := by
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne, ← Finset.nonempty_iff_ne_empty]
    rcases hfree with hf | hf | hf
    · exact ⟨i, Finset.mem_filter.2 ⟨by simp, hf⟩⟩
    · exact ⟨j, Finset.mem_filter.2 ⟨by simp, hf⟩⟩
    · exact ⟨k, Finset.mem_filter.2 ⟨by simp, hf⟩⟩
  have hG : GPGood F {i, j, k} := ⟨by omega, by omega⟩
  let lam : ι → ℝ := fun m => if m = i then a else if m = j then b else c
  have hli : lam i = a := by simp [lam]
  have hlj : lam j = b := by simp [lam, Ne.symm hij]
  have hlk : lam k = c := by simp [lam, Ne.symm hik, Ne.symm hjk]
  have h3 := h {i, j, k} (Finset.subset_univ _) hG lam
    (by rw [Finset.sum_insert hi', Finset.sum_pair hjk, hli, hlj, hlk, ← add_assoc]; exact habc)
    (by rw [Finset.sum_insert hi', Finset.sum_pair hjk, hli, hlj, hlk, ← add_assoc]; exact hcomb)
  exact ⟨hli ▸ h3 i (by simp), hlj ▸ h3 j (by simp), hlk ▸ h3 k (by simp)⟩

/-- Four distinct indices with at most two fixed ones (one free index in each pair): affinely
independent (weight form). -/
lemma GPInv.indep4 (h : GPInv F w Finset.univ) {i j k l : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) (hf1 : i ∉ F ∨ j ∉ F)
    (hf2 : k ∉ F ∨ l ∉ F) :
    ∀ a b c e : ℝ, a + b + c + e = 0 → a • w i + b • w j + c • w k + e • w l = 0 →
      a = 0 ∧ b = 0 ∧ c = 0 ∧ e = 0 := by
  intro a b c e habce hcomb
  have hk' : k ∉ ({l} : Finset ι) := by simpa using hkl
  have hj' : j ∉ ({k, l} : Finset ι) := by simp [hjk, hjl]
  have hi' : i ∉ ({j, k, l} : Finset ι) := by simp [hij, hik, hil]
  have hcard : ({i, j, k, l} : Finset ι).card = 4 := by
    rw [Finset.card_insert_of_notMem hi', Finset.card_insert_of_notMem hj', Finset.card_pair hkl]
  have hfc : 2 ≤ (({i, j, k, l} : Finset ι).filter (· ∉ F)).card := by
    obtain ⟨x, hx, hxF⟩ : ∃ x, (x = i ∨ x = j) ∧ x ∉ F := by
      rcases hf1 with hf | hf
      · exact ⟨i, Or.inl rfl, hf⟩
      · exact ⟨j, Or.inr rfl, hf⟩
    obtain ⟨y, hy, hyF⟩ : ∃ y, (y = k ∨ y = l) ∧ y ∉ F := by
      rcases hf2 with hf | hf
      · exact ⟨k, Or.inl rfl, hf⟩
      · exact ⟨l, Or.inr rfl, hf⟩
    have hxy : x ≠ y := by
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> assumption
    have hsub : ({x, y} : Finset ι) ⊆ ({i, j, k, l} : Finset ι).filter (· ∉ F) := by
      intro z hz
      rw [Finset.mem_filter]
      rcases Finset.mem_insert.1 hz with rfl | hz
      · refine ⟨?_, hxF⟩
        rcases hx with rfl | rfl <;> simp
      · rw [Finset.mem_singleton.1 hz]
        refine ⟨?_, hyF⟩
        rcases hy with rfl | rfl <;> simp
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair hxy] at this
  have hG : GPGood F {i, j, k, l} := ⟨by omega, by omega⟩
  let lam : ι → ℝ := fun m => if m = i then a else if m = j then b else if m = k then c else e
  have hli : lam i = a := by simp [lam]
  have hlj : lam j = b := by simp [lam, Ne.symm hij]
  have hlk : lam k = c := by simp [lam, Ne.symm hik, Ne.symm hjk]
  have hll : lam l = e := by simp [lam, Ne.symm hil, Ne.symm hjl, Ne.symm hkl]
  have h4 := h {i, j, k, l} (Finset.subset_univ _) hG lam
    (by
      rw [Finset.sum_insert hi', Finset.sum_insert hj', Finset.sum_pair hkl, hli, hlj, hlk, hll]
      linarith)
    (by
      rw [Finset.sum_insert hi', Finset.sum_insert hj', Finset.sum_pair hkl, hli, hlj, hlk, hll,
        ← hcomb]
      abel)
  exact ⟨hli ▸ h4 i (by simp), hlj ▸ h4 j (by simp), hlk ▸ h4 k (by simp),
    hll ▸ h4 l (by simp)⟩

end Consequences

/-! ### Constants and the statement -/

/-- The constant `c₀ = 3^{-d} d^{-d/2}` of the blueprint (`b:lem-gp`). -/
def gpC0 (d : ℕ) : ℝ := (3 : ℝ) ^ (-(d : ℝ)) * (d : ℝ) ^ (-(d : ℝ) / 2)

/-- The separation constant `c₁ = (2R₀ + 2)^{-2}` of the blueprint (`b:lem-gp`). -/
def gpC1 (R₀ : ℝ) : ℝ := ((2 * R₀ + 2) ^ 2)⁻¹

lemma gpC0_pos (hd : 1 ≤ d) : 0 < gpC0 d := by
  have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold gpC0; positivity

lemma gpC1_pos {R₀ : ℝ} (hR₀ : 0 ≤ R₀) : 0 < gpC1 R₀ := by
  unfold gpC1; positivity

/-- `c₀ ≤ 1/√d`. -/
lemma gpC0_le (hd : 1 ≤ d) : gpC0 d ≤ (√(d : ℝ))⁻¹ := by
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h3 : (3 : ℝ) ^ (-(d : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  have hdd : (d : ℝ) ^ (-(d : ℝ) / 2) ≤ (d : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hd0 (by linarith)
  have hsq : (d : ℝ) ^ (-(1 / 2 : ℝ)) = (√(d : ℝ))⁻¹ := by
    rw [Real.rpow_neg (by linarith), Real.sqrt_eq_rpow]
  have hpos : 0 ≤ (d : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
  unfold gpC0
  calc (3 : ℝ) ^ (-(d : ℝ)) * (d : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 * (d : ℝ) ^ (-(d : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right h3 hpos
    _ ≤ (√(d : ℝ))⁻¹ := by rw [one_mul, ← hsq]; exact hdd

/-- The hypothesis `ν ≤ c₀ δ/(n + 1)³` gives the hypothesis of `gp_core`. -/
lemma gp_hyp_of_le (hd : 1 ≤ d) {ν δ : ℝ} {n : ℕ} (hν : 0 < ν) (hδ : 0 ≤ δ)
    (hνδ : ν ≤ gpC0 d * δ / ((n : ℝ) + 1) ^ 3) :
    √(d : ℝ) * ν * ((n : ℝ) ^ 3 + 1) ≤ δ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hs : 0 < √(d : ℝ) := Real.sqrt_pos.2 hd0
  have hn : (0 : ℝ) < ((n : ℝ) + 1) ^ 3 := by positivity
  have h1 : ν ≤ (√(d : ℝ))⁻¹ * δ / ((n : ℝ) + 1) ^ 3 :=
    hνδ.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (gpC0_le hd) hδ) hn.le)
  have h2 : (n : ℝ) ^ 3 + 1 ≤ ((n : ℝ) + 1) ^ 3 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [sq_nonneg (n : ℝ)]
  rw [le_div_iff₀ hn] at h1
  calc √(d : ℝ) * ν * ((n : ℝ) ^ 3 + 1) ≤ √(d : ℝ) * ν * ((n : ℝ) + 1) ^ 3 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = √(d : ℝ) * (ν * ((n : ℝ) + 1) ^ 3) := by ring
    _ ≤ √(d : ℝ) * ((√(d : ℝ))⁻¹ * δ) := mul_le_mul_of_nonneg_left h1 hs.le
    _ = δ := by field_simp

/-- **Rational general position, explicit constants** (blueprint `b:lem-gp`, `d ≥ 3`;
`c₀ = gpC0 d = 3^{-d}d^{-d/2}`, `c₁ = gpC1 R₀ = (2R₀ + 2)^{-2}`; unordered edges). -/
theorem rational_general_position_explicit (hd : 3 ≤ d) {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {n : ℕ}
    (v : Fin n → Rd d) (E : Finset (Sym2 (Fin n))) (fixed : Finset (Fin n)) {ν δ : ℝ} (o : Rd d)
    (hν : 0 < ν) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hνδ : ν ≤ gpC0 d * δ / ((n : ℝ) + 1) ^ 3)
    (hv : ∀ i, ‖v i‖ ≤ R₀) (hfix : ∀ i ∈ fixed, OnGrid ν o (v i)) (hinj : Set.InjOn v fixed)
    (hE : ∀ i j, s(i, j) ∈ E → i ∉ fixed ∨ j ∉ fixed) :
    ∃ w : Fin n → Rd d, (∀ i ∈ fixed, w i = v i) ∧ (∀ i, ‖w i - v i‖ ≤ δ) ∧
      (∀ i, OnGrid ν o (w i)) ∧ Function.Injective w ∧
      (∀ i j k, s(i, j) ∈ E → s(j, k) ∈ E → i ≠ j → j ≠ k → i ≠ k →
        ¬ Collinear ℝ {w i, w j, w k} ∧
          segment ℝ (w i) (w j) ∩ segment ℝ (w j) (w k) = {w j}) ∧
      (∀ i j k l, s(i, j) ∈ E → s(k, l) ∈ E → i ≠ j → k ≠ l → i ≠ k → i ≠ l → j ≠ k →
        j ≠ l → ∀ p ∈ segment ℝ (w i) (w j), ∀ q ∈ segment ℝ (w k) (w l),
          gpC1 R₀ * ν ^ 3 ≤ dist p q) := by
  have hcore := gp_hyp_of_le (by omega) hν hδ.le hνδ
  rw [← Fintype.card_fin n] at hcore
  obtain ⟨w, hwF, hwv, hwg, hwI⟩ := gp_core hd v fixed o hν hcore hfix hinj
  have hwR : ∀ i, ‖w i‖ ≤ R₀ + 1 := fun i => by
    have h1 := norm_le_insert' (w i) (v i)
    have h2 := hwv i
    have h3 := hv i
    linarith [norm_sub_norm_le (w i) (v i)]
  have hdiff : ∀ i j, ‖w i - w j‖ ≤ 2 * R₀ + 2 := fun i j =>
    (norm_sub_le _ _).trans (by linarith [hwR i, hwR j])
  refine ⟨w, hwF, hwv, hwg, hwI.injective, ?_, ?_⟩
  · intro i j k hij hjk hij' hjk' hik'
    have hfree : i ∉ fixed ∨ j ∉ fixed ∨ k ∉ fixed := by
      rcases hE i j hij with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have h3 := hwI.indep3 hij' hik' hjk' hfree
    exact ⟨not_collinear_of_indep3 h3, segment_inter_segment_eq h3⟩
  · intro i j k l hij hkl hij' hkl' hik hil hjk hjl p hp q hq
    have h4 := hwI.indep4 hij' hik hil hjk hjl hkl' (hE i j hij) (hE k l hkl)
    have hsep := grid_segment_sep hν (hwg i) (hwg j) (hwg k) (hwg l) h4 hp hq
    have hL : 0 < 2 * R₀ + 2 := by linarith
    have hprod : ‖w j - w i‖ * ‖w l - w k‖ ≤ (2 * R₀ + 2) ^ 2 := by
      rw [sq]
      exact mul_le_mul (hdiff j i) (hdiff l k) (norm_nonneg _) hL.le
    have hdist : 0 ≤ dist p q := dist_nonneg
    unfold gpC1
    rw [inv_mul_le_iff₀ (by positivity)]
    calc ν ^ 3 ≤ dist p q * ‖w j - w i‖ * ‖w l - w k‖ := hsep
      _ = dist p q * (‖w j - w i‖ * ‖w l - w k‖) := by ring
      _ ≤ dist p q * (2 * R₀ + 2) ^ 2 := mul_le_mul_of_nonneg_left hprod hdist
      _ = (2 * R₀ + 2) ^ 2 * dist p q := by ring

/-- **Rational general position** (NA2 probe quantifier shape, with the blueprint's unordered
edges; `d ≥ 3`): free vertices can be moved by at most `δ` onto the grid `o + νℤ^d` so that the
vertices are distinct, incident edges meet only at their common vertex, and edges without a common
vertex are at distance `≥ c₁ ν³`, provided `ν ≤ c₀ δ/(n + 1)³`. -/
theorem rational_general_position (hd : 3 ≤ d) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
    ∀ (n : ℕ) (v : Fin n → Rd d) (E : Finset (Sym2 (Fin n))) (fixed : Finset (Fin n))
      (ν δ : ℝ) (o : Rd d), 0 < ν → 0 < δ → δ ≤ 1 → ν ≤ c₀ * δ / ((n : ℝ) + 1) ^ 3 →
      E.card ≤ n → (∀ i, ‖v i‖ ≤ R₀) → (∀ i ∈ fixed, OnGrid ν o (v i)) →
      Set.InjOn v fixed → (∀ i j, s(i, j) ∈ E → i ≠ j ∧ (i ∉ fixed ∨ j ∉ fixed)) →
      ∃ w : Fin n → Rd d, (∀ i ∈ fixed, w i = v i) ∧ (∀ i, ‖w i - v i‖ ≤ δ) ∧
        (∀ i, OnGrid ν o (w i)) ∧ Function.Injective w ∧
        (∀ i j k l, s(i, j) ∈ E → s(k, l) ∈ E → i ≠ k → i ≠ l → j ≠ k → j ≠ l →
          ∀ p ∈ segment ℝ (w i) (w j), ∀ q ∈ segment ℝ (w k) (w l), c₁ * ν ^ 3 ≤ dist p q) ∧
        (∀ i j k, s(i, j) ∈ E → s(j, k) ∈ E → i ≠ k →
          segment ℝ (w i) (w j) ∩ segment ℝ (w j) (w k) = {w j}) := by
  refine ⟨gpC0 d, gpC1 R₀, gpC0_pos (by omega), gpC1_pos hR₀.le, ?_⟩
  intro n v E fixed ν δ o hν hδ hδ1 hνδ _ hv hfix hinj hE
  obtain ⟨w, hwF, hwv, hwg, hwinj, hinc, hsep⟩ := rational_general_position_explicit hd hR₀.le
    v E fixed o hν hδ hδ1 hνδ hv hfix hinj fun i j h => (hE i j h).2
  refine ⟨w, hwF, hwv, hwg, hwinj, fun i j k l hij hkl hik hil hjk hjl => ?_,
    fun i j k hij hjk hik => ?_⟩
  · exact hsep i j k l hij hkl (hE i j hij).1 (hE k l hkl).1 hik hil hjk hjl
  · exact (hinc i j k hij hjk (hE i j hij).1 (hE j k hjk).1 hik).2

/-! ### Segment statements from the invariant -/

section SegmentConsequences

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Finset ι} {w : ι → Rd d}

/-- Segments of four distinct indices (each pair with a free index) are `≥ c₁ν³` apart when all
points are on the grid and in `B̄(0, R₀ + 1)`. -/
lemma GPInv.segment_sep (h : GPInv F w Finset.univ) {ν R₀ : ℝ} (hν : 0 < ν) (hR₀ : 0 ≤ R₀)
    {o : Rd d} (hg : ∀ i, OnGrid ν o (w i)) (hw : ∀ i, ‖w i‖ ≤ R₀ + 1) {i j k l : ι}
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hf1 : i ∉ F ∨ j ∉ F) (hf2 : k ∉ F ∨ l ∉ F) :
    ∀ p ∈ segment ℝ (w i) (w j), ∀ q ∈ segment ℝ (w k) (w l), gpC1 R₀ * ν ^ 3 ≤ dist p q := by
  intro p hp q hq
  have h4 := h.indep4 hij hik hil hjk hjl hkl hf1 hf2
  have hsep := grid_segment_sep hν (hg i) (hg j) (hg k) (hg l) h4 hp hq
  have hdiff : ∀ a b, ‖w a - w b‖ ≤ 2 * R₀ + 2 := fun a b =>
    (norm_sub_le _ _).trans (by linarith [hw a, hw b])
  have hL : 0 < 2 * R₀ + 2 := by linarith
  have hprod : ‖w j - w i‖ * ‖w l - w k‖ ≤ (2 * R₀ + 2) ^ 2 := by
    rw [sq]
    exact mul_le_mul (hdiff j i) (hdiff l k) (norm_nonneg _) hL.le
  have hdist : 0 ≤ dist p q := dist_nonneg
  unfold gpC1
  rw [inv_mul_le_iff₀ (by positivity)]
  calc ν ^ 3 ≤ dist p q * ‖w j - w i‖ * ‖w l - w k‖ := hsep
    _ = dist p q * (‖w j - w i‖ * ‖w l - w k‖) := by ring
    _ ≤ dist p q * (2 * R₀ + 2) ^ 2 := mul_le_mul_of_nonneg_left hprod hdist
    _ = (2 * R₀ + 2) ^ 2 * dist p q := by ring

/-- Incident segments of three distinct indices, not all fixed, meet only at the common vertex. -/
lemma GPInv.segment_inter (h : GPInv F w Finset.univ) {i j k : ι} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (hfree : i ∉ F ∨ j ∉ F ∨ k ∉ F) :
    segment ℝ (w i) (w j) ∩ segment ℝ (w j) (w k) = {w j} :=
  segment_inter_segment_eq (h.indep3 hij hik hjk hfree)

/-- **Rational general position, ordered edges** (the NA2 probe shape, corrected): the probe's
incident clause gets the extra hypothesis `e.1 ≠ e'.2` (without it the reversed pair
`e = (0, 1)`, `e' = (1, 0)` is a counterexample, see the module docstring). -/
theorem rational_general_position_ordered (hd : 3 ≤ d) {R₀ : ℝ} (hR₀ : 0 < R₀) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
    ∀ (n : ℕ) (v : Fin n → Rd d) (E : Finset (Fin n × Fin n)) (fixed : Finset (Fin n))
      (ν δ : ℝ) (o : Rd d), 0 < ν → 0 < δ → δ ≤ 1 → ν ≤ c₀ * δ / ((n : ℝ) + 1) ^ 3 →
      E.card ≤ n → (∀ i, ‖v i‖ ≤ R₀) → (∀ i ∈ fixed, OnGrid ν o (v i)) →
      Set.InjOn v fixed → (∀ e ∈ E, e.1 ≠ e.2 ∧ (e.1 ∉ fixed ∨ e.2 ∉ fixed)) →
      ∃ w : Fin n → Rd d, (∀ i ∈ fixed, w i = v i) ∧ (∀ i, ‖w i - v i‖ ≤ δ) ∧
        (∀ i, OnGrid ν o (w i)) ∧
        (∀ e ∈ E, ∀ e' ∈ E, e.1 ≠ e'.1 → e.1 ≠ e'.2 → e.2 ≠ e'.1 → e.2 ≠ e'.2 →
          ∀ p ∈ segment ℝ (w e.1) (w e.2), ∀ q ∈ segment ℝ (w e'.1) (w e'.2),
            c₁ * ν ^ 3 ≤ dist p q) ∧
        (∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → e.2 = e'.1 → e.1 ≠ e'.2 →
          segment ℝ (w e.1) (w e.2) ∩ segment ℝ (w e'.1) (w e'.2) = {w e.2}) := by
  refine ⟨gpC0 d, gpC1 R₀, gpC0_pos (by omega), gpC1_pos hR₀.le, ?_⟩
  intro n v E fixed ν δ o hν hδ hδ1 hνδ _ hv hfix hinj hE
  have hcore := gp_hyp_of_le (by omega) hν hδ.le hνδ
  rw [← Fintype.card_fin n] at hcore
  obtain ⟨w, hwF, hwv, hwg, hwI⟩ := gp_core hd v fixed o hν hcore hfix hinj
  have hwR : ∀ i, ‖w i‖ ≤ R₀ + 1 := fun i => by
    have h1 := norm_sub_norm_le (w i) (v i)
    linarith [hwv i, hv i]
  refine ⟨w, hwF, hwv, hwg, fun e he e' he' h1 h2 h3 h4 => ?_, fun e he e' he' _ h12 h3 => ?_⟩
  · exact hwI.segment_sep hν hR₀.le hwg hwR (hE e he).1 h1 h2 h3 h4 (hE e' he').1 (hE e he).2
      (hE e' he').2
  · rw [h12]
    have hne' := (hE e' he').1
    have hne := (hE e he).1
    rw [h12] at hne
    refine hwI.segment_inter hne h3 hne' ?_
    rcases (hE e he).2 with h | h
    · exact Or.inl h
    · rw [h12] at h; exact Or.inr (Or.inl h)

end SegmentConsequences

end HigherDimLQGContinuity.Routing

end
