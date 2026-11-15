/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Ito.FiltrationBasic
import InteractingSLE.Spec.Coupling.Assembly11BCoord
import InteractingSLE.Spec.Sec7.LocalExtNRef

/-!
# Usual-augmentation stopping times on a product with an independent factor

Packet PROVE-ZHAN-A1CANON. A.1's reference space is the coupling space `X` times an independent Wiener factor `Y`
(the continuation of the image noise after the first contact, follow-up 4 §2.5, R71; A1REF-CD's `reference_glue`). The
curves' filtrations are pulled back from `X`, but the usual augmentation (R70) adds the null sets of the product, so a
stopping time `τ` of the augmented pullback need not be a function of the first coordinate. This file shows that it is
one up to a null set, and that its stopped σ-algebra is the pullback of the factor's up to null sets:

* `exists_ae_eq_of_measurableSet_sup_nullSets`: a set of `m ⊔ 𝒩_P` is a.e. equal to a set of `m`;
  `measurableSet_of_ae_eq_of_nullSets_le`: a measurable set a.e. equal to a set of a σ-algebra containing `𝒩_P` is
  in it;
* `ae_section_ae_eq`: if `E =ᵐ Prod.fst ⁻¹' A` on `X × Y`, almost every section of `E` is a.e. equal to `A` (Fubini);
* `measurableSet_usualAugmentation_of_nnrat`: monotone families measurable in `𝓕_r ∨ 𝒩` for rational `q < r` give
  sets of the usual augmentation;
* `comap_usualAugmentation_le`: the pullback of `usualAugmentation 𝓕 μ` is below the usual augmentation of the pullback;
* **`exists_factor_stoppingTime`**: every stopping time `τ` of `usualAugmentation (𝓕 ∘ fst) (μ ⊗ ν)` agrees a.e. with
  `τ' ∘ fst` for a stopping time `τ'` of `usualAugmentation 𝓕 μ`, and every event of the stopped σ-algebra of `τ` is
  a.e. the preimage of an event of the stopped σ-algebra of `τ'`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Canon

/-! ### Null-set closure -/

section Null

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The measurable sets a.e. equal to a set of `m` (a σ-algebra). -/
@[instance_reducible]
def aeClosure (P : Measure Ω) (m : MeasurableSpace Ω) : MeasurableSpace Ω where
  MeasurableSet' s := MeasurableSet[mΩ] s ∧ ∃ s', MeasurableSet[m] s' ∧ s =ᵐ[P] s'
  measurableSet_empty := ⟨@MeasurableSet.empty _ mΩ, ∅, @MeasurableSet.empty _ m, ae_eq_refl _⟩
  measurableSet_compl s hs := by
    obtain ⟨hs, s', hs', h⟩ := hs
    exact ⟨@MeasurableSet.compl _ _ mΩ hs, s'ᶜ, hs'.compl, ae_eq_set_compl_compl.2 h⟩
  measurableSet_iUnion f hf := by
    choose hm s' hs' h using hf
    exact ⟨@MeasurableSet.iUnion _ _ mΩ _ _ hm, ⋃ i, s' i, MeasurableSet.iUnion hs',
      EventuallyEqSet.countable_iUnion h⟩

/-- **A set of `m ⊔ 𝒩_P` is a.e. equal to a set of `m`.** -/
theorem exists_ae_eq_of_measurableSet_sup_nullSets {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {s : Set Ω}
    (hs : MeasurableSet[m ⊔ Ito.nullSets P] s) : ∃ s', MeasurableSet[m] s' ∧ s =ᵐ[P] s' := by
  have hle : m ⊔ Ito.nullSets P ≤ @aeClosure Ω mΩ P m := by
    refine sup_le (fun t ht => ⟨hm t ht, t, ht, ae_eq_refl _⟩) ?_
    refine MeasurableSpace.generateFrom_le fun t ht => ⟨ht.1, ∅, @MeasurableSet.empty _ m, ?_⟩
    exact ae_eq_empty.2 ht.2
  exact (hle s hs).2

/-- **A measurable set a.e. equal to a set of a σ-algebra `𝓜 ⊇ 𝒩_P` is in `𝓜`.** -/
theorem measurableSet_of_ae_eq_of_nullSets_le {𝓜 : MeasurableSpace Ω} (h𝓜 : 𝓜 ≤ mΩ)
    (hN : Ito.nullSets P ≤ 𝓜) {s t : Set Ω} (hs : MeasurableSet[mΩ] s) (ht : MeasurableSet[𝓜] t)
    (h : s =ᵐ[P] t) : MeasurableSet[𝓜] s := by
  obtain ⟨h1, h2⟩ := ae_eq_set.1 h
  have htm : MeasurableSet[mΩ] t := h𝓜 t ht
  have hn1 : MeasurableSet[𝓜] (s \ t) := hN _ (MeasurableSpace.measurableSet_generateFrom ⟨hs.diff htm, h1⟩)
  have hn2 : MeasurableSet[𝓜] (t \ s) := hN _ (MeasurableSpace.measurableSet_generateFrom ⟨htm.diff hs, h2⟩)
  have e : s = (t \ (t \ s)) ∪ (s \ t) := by
    ext ω
    by_cases h1 : ω ∈ s <;> by_cases h2 : ω ∈ t <;> simp [h1, h2]
  rw [e]
  exact (ht.diff hn2).union hn1

/-- A measurable function a.e. equal to an `𝓜`-measurable one is `𝓜`-measurable (`𝓜 ⊇ 𝒩_P`). -/
theorem measurable_of_ae_eq_of_nullSets_le {β : Type*} [MeasurableSpace β] {𝓜 : MeasurableSpace Ω}
    (h𝓜 : 𝓜 ≤ mΩ) (hN : Ito.nullSets P ≤ 𝓜) {f g : Ω → β} (hf : Measurable[mΩ] f) (hg : Measurable[𝓜] g)
    (h : f =ᵐ[P] g) : Measurable[𝓜] f := fun A hA =>
  @measurableSet_of_ae_eq_of_nullSets_le Ω mΩ P 𝓜 h𝓜 hN _ _ (hf hA) (hg hA) (h.fun_comp (· ∈ A))

end Null

/-! ### Rational approximation -/

section Rat

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem exists_nnrat_btwn {a b : ℝ≥0} (h : a < b) : ∃ q : ℚ≥0, a < q ∧ (q : ℝ≥0) < b := by
  obtain ⟨_, ⟨q, rfl⟩, hq⟩ := LocalExt.dense_range_coe_nnrat.exists_between h
  exact ⟨q, hq⟩

theorem eq_of_forall_nnrat_le_iff {a b : ℝ≥0} (h : ∀ q : ℚ≥0, a ≤ q ↔ b ≤ q) : a = b := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hab | hba
  · obtain ⟨q, h1, h2⟩ := exists_nnrat_btwn hab
    exact absurd ((h q).1 h1.le) (not_le.2 h2)
  · obtain ⟨q, h1, h2⟩ := exists_nnrat_btwn hba
    exact absurd ((h q).2 h1.le) (not_le.2 h2)

theorem le_iff_forall_nnrat {a t : ℝ≥0} : a ≤ t ↔ ∀ q : ℚ≥0, t < q → a ≤ q := by
  refine ⟨fun h q hq => h.trans hq.le, fun h => ?_⟩
  by_contra hlt
  obtain ⟨q, h1, h2⟩ := exists_nnrat_btwn (not_le.1 hlt)
  exact absurd (h q h1) (not_le.2 h2)

/-- **Sets of the usual augmentation from rational approximations**: if `f` is monotone, `f q` is measurable for
`𝓕_r ∨ 𝒩_P` whenever `q < r` are rational, and `C = ⋂_{q > t} f q`, then `C` is in the usual augmentation at `t`. -/
theorem measurableSet_usualAugmentation_of_nnrat {𝓕 : Filtration ℝ≥0 mΩ} {f : ℚ≥0 → Set Ω} (hmono : Monotone f)
    (h : ∀ q r : ℚ≥0, q < r → MeasurableSet[Ito.nullAugmented 𝓕 P r] (f q)) {C : Set Ω} {t : ℝ≥0}
    (hC : ∀ ω, ω ∈ C ↔ ∀ q : ℚ≥0, t < q → ω ∈ f q) : MeasurableSet[usualAugmentation 𝓕 P t] C := by
  rw [Ito.usualAugmentation_apply]
  refine MeasurableSpace.measurableSet_iInf.2 fun u => MeasurableSpace.measurableSet_iInf.2 fun hu => ?_
  obtain ⟨r, htr, hru⟩ := exists_nnrat_btwn hu
  have e : C = ⋂ (q : {q : ℚ≥0 // t < q ∧ q < r}), f q := by
    ext ω
    simp only [mem_iInter, hC]
    refine ⟨fun H q => H q q.2.1, fun H q hq => ?_⟩
    obtain ⟨q', h1, h2⟩ := exists_nnrat_btwn (lt_min hq htr)
    have hq'r : q' < r := by exact_mod_cast h2.trans_le (min_le_right _ _)
    have hq'q : q' ≤ q := by exact_mod_cast (h2.trans_le (min_le_left _ _)).le
    exact hmono hq'q (H ⟨q', h1, hq'r⟩)
  rw [e]
  refine MeasurableSet.iInter fun q => ?_
  have hle : Ito.nullAugmented 𝓕 P r ≤ Ito.nullAugmented 𝓕 P u := (Ito.nullAugmented 𝓕 P).mono hru.le
  exact hle _ (h q r q.2.2)

end Rat

/-! ### The product with an independent factor -/

section Product

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}

/-- Sections of measurable sets are measurable. -/
theorem measurableSet_section {E : Set (X × Y)} (hE : MeasurableSet E) (y : Y) :
    MeasurableSet ((fun x => (x, y)) ⁻¹' E) := measurable_prodMk_right hE

/-- **Almost every section of a set a.e. equal to a cylinder `A × Y` is a.e. equal to `A`** (Fubini). -/
theorem ae_section_ae_eq [SFinite μ] [SFinite ν] {E : Set (X × Y)} {A : Set X} (hE : MeasurableSet E)
    (hA : MeasurableSet A) (h : E =ᵐ[μ.prod ν] Prod.fst ⁻¹' A) :
    ∀ᵐ y ∂ν, (fun x => (x, y)) ⁻¹' E =ᵐ[μ] A := by
  obtain ⟨h1, h2⟩ := ae_eq_set.1 h
  have hD : MeasurableSet (E \ Prod.fst ⁻¹' A ∪ Prod.fst ⁻¹' A \ E) :=
    (hE.diff (measurable_fst hA)).union ((measurable_fst hA).diff hE)
  have h0 : (μ.prod ν) (E \ Prod.fst ⁻¹' A ∪ Prod.fst ⁻¹' A \ E) = 0 :=
    measure_union_null h1 h2
  rw [Measure.prod_apply_symm hD, lintegral_eq_zero_iff (measurable_measure_prodMk_right hD)] at h0
  filter_upwards [h0] with y hy
  refine ae_eq_set.2 ⟨measure_mono_null (fun x hx => ?_) hy, measure_mono_null (fun x hx => ?_) hy⟩
  · exact Or.inl ⟨hx.1, hx.2⟩
  · exact Or.inr ⟨hx.1, hx.2⟩

/-- The pullback of the `μ`-null σ-algebra is below the `μ ⊗ ν`-null σ-algebra. -/
theorem comap_nullSets_le [SFinite ν] :
    (Ito.nullSets μ).comap Prod.fst ≤ Ito.nullSets (μ.prod ν) := by
  unfold Ito.nullSets
  rw [MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le fun t ht => ?_
  obtain ⟨s, ⟨hs, hs0⟩, rfl⟩ := ht
  refine MeasurableSpace.measurableSet_generateFrom ⟨measurable_fst hs, ?_⟩
  have e : Prod.fst ⁻¹' s = s ×ˢ (univ : Set Y) := by ext; simp
  rw [e, Measure.prod_prod, hs0, zero_mul]

variable (𝓕 : Filtration ℝ≥0 mX)

/-- **The pullback of the usual augmentation is below the usual augmentation of the pullback.** -/
theorem comap_usualAugmentation_le [SFinite ν] (t : ℝ≥0) :
    (usualAugmentation 𝓕 μ t).comap Prod.fst ≤
      usualAugmentation (Coupling.filtrationComap 𝓕 (measurable_fst : Measurable (Prod.fst : X × Y → X)))
        (μ.prod ν) t := by
  rw [Ito.usualAugmentation_apply, Ito.usualAugmentation_apply]
  refine le_iInf₂ fun u hu => (MeasurableSpace.comap_mono (iInf₂_le u hu)).trans ?_
  rw [Ito.nullAugmented_apply, Ito.nullAugmented_apply, MeasurableSpace.comap_sup]
  exact sup_le_sup le_rfl comap_nullSets_le

variable {𝓕}

/-- A set of the usual augmentation of the pullback at `t` is a.e. the preimage of a set of `𝓕_s`, `s > t`. -/
theorem exists_fst_of_usualAugmentation {E : Set (X × Y)} {t s : ℝ≥0} (hts : t < s)
    (hE : MeasurableSet[usualAugmentation (Coupling.filtrationComap 𝓕
      (measurable_fst : Measurable (Prod.fst : X × Y → X))) (μ.prod ν) t] E) :
    ∃ A, MeasurableSet[𝓕 s] A ∧ E =ᵐ[μ.prod ν] Prod.fst ⁻¹' A := by
  rw [Ito.usualAugmentation_apply] at hE
  have hE' := (MeasurableSpace.measurableSet_iInf.1 (MeasurableSpace.measurableSet_iInf.1 hE s) hts)
  rw [Ito.nullAugmented_apply] at hE'
  obtain ⟨s', hs', h⟩ := exists_ae_eq_of_measurableSet_sup_nullSets
    ((Coupling.filtrationComap 𝓕 (measurable_fst : Measurable (Prod.fst : X × Y → X))).le s) hE'
  obtain ⟨A, hA, rfl⟩ := hs'
  exact ⟨A, hA, h⟩

end Product

/-! ### Factorization of stopping times -/

section Factor

variable {X Y : Type*} [mX : MeasurableSpace X] [mY : MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {𝓕 : Filtration ℝ≥0 mX}

/-- **Usual-augmentation stopping times on `X × Y` factor through `X` up to null sets.** A stopping time `τ` of the
usual augmentation of `𝓕 ∘ fst` under `μ ⊗ ν` agrees a.e. with `τ' ∘ fst` for a stopping time `τ'` of the usual
augmentation of `𝓕` under `μ` (a section of `τ` at a good point of `Y`), and every event of its stopped σ-algebra is
a.e. the preimage of an event of the stopped σ-algebra of `τ'`. -/
theorem exists_factor_stoppingTime {τ : X × Y → ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation (Coupling.filtrationComap 𝓕
      (measurable_fst : Measurable (Prod.fst : X × Y → X))) (μ.prod ν)) fun ω => (τ ω : WithTop ℝ≥0)) :
    ∃ (τ' : X → ℝ≥0) (hτ' : IsStoppingTime (usualAugmentation 𝓕 μ) fun x => (τ' x : WithTop ℝ≥0)),
      (∀ᵐ ω ∂(μ.prod ν), τ ω = τ' ω.1) ∧
      ∀ E, MeasurableSet[hτ.measurableSpace] E →
        ∃ E', MeasurableSet[hτ'.measurableSpace] E' ∧ E =ᵐ[μ.prod ν] Prod.fst ⁻¹' E' := by
  classical
  set 𝓕' := Coupling.filtrationComap 𝓕 (measurable_fst : Measurable (Prod.fst : X × Y → X)) with h𝓕'
  set P := μ.prod ν with hP
  have hna : ∀ r, 𝓕 r ⊔ Ito.nullSets μ ≤ mX := fun r => sup_le (𝓕.le r) (Ito.nullSets_le μ)
  -- the sublevel sets of `τ`
  set L : ℚ≥0 → Set (X × Y) := fun q => {ω | τ ω ≤ (q : ℝ≥0)} with hL
  have hLua : ∀ q : ℚ≥0, MeasurableSet[usualAugmentation 𝓕' P q] (L q) := fun q => by
    have h := hτ (q : ℝ≥0)
    simpa only [WithTop.coe_le_coe] using h
  have hLm : ∀ q, MeasurableSet (L q) := fun q => (usualAugmentation 𝓕' P).le _ _ (hLua q)
  have hK : ∀ q r : ℚ≥0, q < r → ∃ A, MeasurableSet[𝓕 r] A ∧ L q =ᵐ[P] Prod.fst ⁻¹' A :=
    fun q r hqr => exists_fst_of_usualAugmentation (by exact_mod_cast hqr) (hLua q)
  choose! A hAm hAe using hK
  have hgood : ∀ᵐ y ∂ν, ∀ q r : ℚ≥0, q < r → (fun x => (x, y)) ⁻¹' L q =ᵐ[μ] A q r := by
    refine ae_all_iff.2 fun q => ae_all_iff.2 fun r => ?_
    by_cases hqr : q < r
    · filter_upwards [ae_section_ae_eq (hLm q) (𝓕.le _ _ (hAm q r hqr)) (hAe q r hqr)] with y hy _ using hy
    · exact Eventually.of_forall fun y h => absurd h hqr
  obtain ⟨y₀, hy₀⟩ := hgood.exists
  set τ' : X → ℝ≥0 := fun x => τ (x, y₀) with hτ'def
  have hsec : ∀ q : ℚ≥0, {x | τ' x ≤ (q : ℝ≥0)} = (fun x => (x, y₀)) ⁻¹' L q := fun q => rfl
  have hsecm : ∀ q : ℚ≥0, MeasurableSet {x | τ' x ≤ (q : ℝ≥0)} := fun q => by
    rw [hsec]; exact measurableSet_section (hLm q) y₀
  have hτ'na : ∀ q r : ℚ≥0, q < r → MeasurableSet[Ito.nullAugmented 𝓕 μ r] {x | τ' x ≤ (q : ℝ≥0)} := by
    intro q r hqr
    rw [Ito.nullAugmented_apply]
    refine measurableSet_of_ae_eq_of_nullSets_le (hna r) le_sup_right (hsecm q)
      ((le_sup_left : 𝓕 r ≤ 𝓕 r ⊔ Ito.nullSets μ) _ (hAm q r hqr)) ?_
    rw [hsec]; exact hy₀ q r hqr
  have hτ' : IsStoppingTime (usualAugmentation 𝓕 μ) fun x => (τ' x : WithTop ℝ≥0) := by
    intro t
    have e : {x | (τ' x : WithTop ℝ≥0) ≤ t} = {x | τ' x ≤ t} := by ext x; exact WithTop.coe_le_coe
    rw [e]
    refine measurableSet_usualAugmentation_of_nnrat (f := fun q => {x | τ' x ≤ (q : ℝ≥0)}) ?_ hτ'na ?_
    · intro q q' hqq' x hx
      exact (show τ' x ≤ (q : ℝ≥0) from hx).trans (by exact_mod_cast hqq')
    · intro x
      exact le_iff_forall_nnrat
  -- `τ = τ' ∘ fst` almost everywhere
  have hLae : ∀ q : ℚ≥0, L q =ᵐ[P] Prod.fst ⁻¹' {x | τ' x ≤ (q : ℝ≥0)} := by
    intro q
    have hq : q < q + 1 := lt_add_one q
    refine (hAe q (q + 1) hq).trans ?_
    refine Measure.QuasiMeasurePreserving.preimage_ae_eq Measure.quasiMeasurePreserving_fst ?_
    rw [hsec]; exact (hy₀ q (q + 1) hq).symm
  have hae : ∀ᵐ ω ∂P, τ ω = τ' ω.1 := by
    filter_upwards [ae_all_iff.2 hLae] with ω hω
    exact eq_of_forall_nnrat_le_iff fun q => Iff.of_eq (hω q)
  refine ⟨τ', hτ', hae, fun E hE => ?_⟩
  -- the stopped σ-algebra
  have hEm : MeasurableSet E := (iSup_le fun t => (usualAugmentation 𝓕' P).le t) _ hE.1
  set M : ℚ≥0 → Set (X × Y) := fun q => E ∩ L q with hM
  have hMua : ∀ q : ℚ≥0, MeasurableSet[usualAugmentation 𝓕' P q] (M q) := fun q => by
    have h := hE.2 (q : ℝ≥0)
    simpa only [WithTop.coe_le_coe] using h
  have hMm : ∀ q, MeasurableSet (M q) := fun q => (usualAugmentation 𝓕' P).le _ _ (hMua q)
  have hK' : ∀ q r : ℚ≥0, q < r → ∃ A, MeasurableSet[𝓕 r] A ∧ M q =ᵐ[P] Prod.fst ⁻¹' A :=
    fun q r hqr => exists_fst_of_usualAugmentation (by exact_mod_cast hqr) (hMua q)
  choose! A' hA'm hA'e using hK'
  have hEU : E = ⋃ n : ℕ, M (n : ℚ≥0) := by
    ext ω
    simp only [mem_iUnion, hM, hL, mem_inter_iff, Set.mem_ofPred_eq, NNRat.cast_natCast]
    refine ⟨fun h => ?_, fun ⟨n, h, _⟩ => h⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (τ ω)
    exact ⟨n, h, hn⟩
  set E₀ : Set X := ⋃ n : ℕ, A' (n : ℚ≥0) ((n : ℚ≥0) + 1) with hE₀
  have hE₀e : E =ᵐ[P] Prod.fst ⁻¹' E₀ := by
    rw [hE₀, preimage_iUnion]
    conv_lhs => rw [hEU]
    exact EventuallyEqSet.countable_iUnion fun n => hA'e _ _ (lt_add_one _)
  have hE₀m : MeasurableSet E₀ := MeasurableSet.iUnion fun n => 𝓕.le _ _ (hA'm _ _ (lt_add_one _))
  have hgood' : ∀ᵐ y ∂ν, (∀ q r : ℚ≥0, q < r → (fun x => (x, y)) ⁻¹' M q =ᵐ[μ] A' q r) ∧
      (∀ q : ℚ≥0, (fun x => (x, y)) ⁻¹' L q =ᵐ[μ] {x | τ' x ≤ (q : ℝ≥0)}) ∧
      (fun x => (x, y)) ⁻¹' E =ᵐ[μ] E₀ := by
    refine (ae_all_iff.2 fun q => ae_all_iff.2 fun r => ?_).and ((ae_all_iff.2 fun q => ?_).and ?_)
    · by_cases hqr : q < r
      · filter_upwards [ae_section_ae_eq (hMm q) (𝓕.le _ _ (hA'm q r hqr)) (hA'e q r hqr)] with y hy _ using hy
      · exact Eventually.of_forall fun y h => absurd h hqr
    · exact ae_section_ae_eq (hLm q) (hsecm q) (hLae q)
    · exact ae_section_ae_eq hEm hE₀m hE₀e
  obtain ⟨y₁, hy₁M, hy₁L, hy₁E⟩ := hgood'.exists
  set E' : Set X := (fun x => (x, y₁)) ⁻¹' E with hE'
  have hE'm : MeasurableSet E' := measurableSet_section hEm y₁
  have hE'na : ∀ q r : ℚ≥0, q < r →
      MeasurableSet[Ito.nullAugmented 𝓕 μ r] (E' ∩ {x | τ' x ≤ (q : ℝ≥0)}) := by
    intro q r hqr
    rw [Ito.nullAugmented_apply]
    have h1 : E' ∩ {x | τ' x ≤ (q : ℝ≥0)} =ᵐ[μ] (fun x => (x, y₁)) ⁻¹' M q := by
      have e : (fun x => (x, y₁)) ⁻¹' M q = E' ∩ (fun x => (x, y₁)) ⁻¹' L q := rfl
      rw [e]
      exact ae_eq_set_inter (ae_eq_refl E') (hy₁L q).symm
    exact measurableSet_of_ae_eq_of_nullSets_le (hna r) le_sup_right (hE'm.inter (hsecm q))
      ((le_sup_left : 𝓕 r ≤ 𝓕 r ⊔ Ito.nullSets μ) _ (hA'm q r hqr)) (h1.trans (hy₁M q r hqr))
  have hE'i : ∀ t : ℝ≥0, MeasurableSet[usualAugmentation 𝓕 μ t] (E' ∩ {x | (τ' x : WithTop ℝ≥0) ≤ t}) := by
    intro t
    have e : E' ∩ {x | (τ' x : WithTop ℝ≥0) ≤ t} = E' ∩ {x | τ' x ≤ t} := by
      ext x; exact and_congr_right fun _ => WithTop.coe_le_coe
    rw [e]
    refine measurableSet_usualAugmentation_of_nnrat (f := fun q => E' ∩ {x | τ' x ≤ (q : ℝ≥0)}) ?_ hE'na ?_
    · intro q q' hqq' x hx
      exact ⟨hx.1, (show τ' x ≤ (q : ℝ≥0) from hx.2).trans (by exact_mod_cast hqq')⟩
    · intro x
      simp only [mem_inter_iff, Set.mem_ofPred_eq]
      rw [le_iff_forall_nnrat]
      refine ⟨fun ⟨h1, h2⟩ q hq => ⟨h1, h2 q hq⟩, fun h => ?_⟩
      obtain ⟨q, hq, -⟩ := exists_nnrat_btwn (lt_add_one t)
      exact ⟨(h q hq).1, fun q hq => (h q hq).2⟩
  refine ⟨E', ⟨?_, hE'i⟩, ?_⟩
  · have e : E' = ⋃ n : ℕ, E' ∩ {x | (τ' x : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq]
      refine ⟨fun h => ?_, fun ⟨n, h, _⟩ => h⟩
      obtain ⟨n, hn⟩ := exists_nat_ge (τ' x)
      exact ⟨n, h, WithTop.coe_le_coe.2 hn⟩
    rw [e]
    exact MeasurableSet.iUnion fun n =>
      le_iSup (fun t => (usualAugmentation 𝓕 μ t : MeasurableSpace X)) (n : ℝ≥0) _ (hE'i n)
  · exact hE₀e.trans (Measure.QuasiMeasurePreserving.preimage_ae_eq Measure.quasiMeasurePreserving_fst hy₁E.symm)

end Factor

end InteractingSLE.ZhanGT4.A1Canon
