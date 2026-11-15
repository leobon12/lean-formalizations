/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1CanonFactor

/-!
# Usual-augmentation stopping times of a coupling factor through its marginal

Packet PROVE-A1CORE. Source: follow-up 5 §1.3 (`source/external/AstraIG1/ig1_followup5.txt` L203–L216, R73): the
rectangle identity (1.7) is stated at stopping times `τ` of the usual augmentation of the conditioning curve's own
filtration, "The unchanged marginal laws preserve their completed null sets."

On a coupling space `Z` with a measurable projection `π : Z → Y` (the conditioning curve's path) and the pulled-back
filtration `π⁻¹ 𝓕`, a stopping time of the usual augmentation of `π⁻¹ 𝓕` under the coupling `μ` agrees `μ`-a.e. with
`τ' ∘ π` for a stopping time `τ'` of the usual augmentation of `𝓕` under the marginal `μ ∘ π⁻¹`, and every event of
its stopped σ-algebra is a.e. the preimage of an event of the stopped σ-algebra of `τ'`
(**`exists_factor_stoppingTime_map`**). This generalizes A1CANON's `exists_factor_stoppingTime` (product measures,
where a section is taken) to an arbitrary coupling: here the null sets descend through the marginal.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1Core

open A1Canon

section Factor

variable {Z Y : Type*} [mZ : MeasurableSpace Z] [mY : MeasurableSpace Y] {μ : Measure Z} {π : Z → Y}
  {𝓕 : Filtration ℝ≥0 mY}

/-- **Null sets descend through the marginal**: a.e. equal preimages come from a.e. equal sets. -/
theorem ae_eq_of_preimage_ae_eq (hπ : Measurable π) {A B : Set Y} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (h : π ⁻¹' A =ᵐ[μ] π ⁻¹' B) : A =ᵐ[μ.map π] B := by
  rw [ae_eq_set] at h ⊢
  rw [Measure.map_apply hπ (hA.diff hB), Measure.map_apply hπ (hB.diff hA)]
  exact h

theorem preimage_ae_eq_of_ae_eq (hπ : Measurable π) {A B : Set Y} (h : A =ᵐ[μ.map π] B) :
    π ⁻¹' A =ᵐ[μ] π ⁻¹' B :=
  Measure.QuasiMeasurePreserving.preimage_ae_eq ⟨hπ, Measure.AbsolutelyContinuous.rfl⟩ h

/-- A set of the usual augmentation of the pullback at `t` is a.e. the preimage of a set of `𝓕_s`, `s > t`. -/
theorem exists_preimage_of_usualAugmentation (hπ : Measurable π) {E : Set Z} {t s : ℝ≥0} (hts : t < s)
    (hE : MeasurableSet[usualAugmentation (Coupling.filtrationComap 𝓕 hπ) μ t] E) :
    ∃ A, MeasurableSet[𝓕 s] A ∧ E =ᵐ[μ] π ⁻¹' A := by
  rw [Ito.usualAugmentation_apply] at hE
  have hE' := (MeasurableSpace.measurableSet_iInf.1 (MeasurableSpace.measurableSet_iInf.1 hE s) hts)
  rw [Ito.nullAugmented_apply] at hE'
  obtain ⟨s', hs', h⟩ := exists_ae_eq_of_measurableSet_sup_nullSets ((Coupling.filtrationComap 𝓕 hπ).le s) hE'
  obtain ⟨A, hA, rfl⟩ := hs'
  exact ⟨A, hA, h⟩

/-- The pullback of the marginal's null σ-algebra is below the coupling's null σ-algebra. -/
theorem comap_nullSets_le_map (hπ : Measurable π) : (Ito.nullSets (μ.map π)).comap π ≤ Ito.nullSets μ := by
  unfold Ito.nullSets
  rw [MeasurableSpace.comap_generateFrom]
  refine MeasurableSpace.generateFrom_le fun t ht => ?_
  obtain ⟨s, ⟨hs, hs0⟩, rfl⟩ := ht
  refine MeasurableSpace.measurableSet_generateFrom ⟨hπ hs, ?_⟩
  rwa [Measure.map_apply hπ hs] at hs0

/-- **The pullback of the marginal's usual augmentation is below the coupling's usual augmentation** of the
pulled-back filtration. -/
theorem comap_usualAugmentation_le_map (hπ : Measurable π) (t : ℝ≥0) :
    (usualAugmentation 𝓕 (μ.map π) t).comap π ≤ usualAugmentation (Coupling.filtrationComap 𝓕 hπ) μ t := by
  rw [Ito.usualAugmentation_apply, Ito.usualAugmentation_apply]
  refine le_iInf₂ fun u hu => (MeasurableSpace.comap_mono (iInf₂_le u hu)).trans ?_
  rw [Ito.nullAugmented_apply, Ito.nullAugmented_apply, MeasurableSpace.comap_sup]
  exact sup_le_sup le_rfl (comap_nullSets_le_map hπ)


/-- The infimum of the rational levels of a monotone family of sets covering `Y`. -/
def levelInf (G : ℚ≥0 → Set Y) (y : Y) : ℝ≥0 := sInf ((fun q : ℚ≥0 => (q : ℝ≥0)) '' {q | y ∈ G q})

omit mY in
theorem levelInf_le_iff {G : ℚ≥0 → Set Y} (hG : Monotone G) {y : Y} (hy : ∃ q, y ∈ G q) (t : ℝ≥0) :
    levelInf G y ≤ t ↔ ∀ q : ℚ≥0, t < q → y ∈ G q := by
  have hne : ((fun q : ℚ≥0 => (q : ℝ≥0)) '' {q | y ∈ G q}).Nonempty := by
    obtain ⟨q, hq⟩ := hy; exact ⟨q, q, hq, rfl⟩
  have hbdd : BddBelow ((fun q : ℚ≥0 => (q : ℝ≥0)) '' {q | y ∈ G q}) := OrderBot.bddBelow _
  constructor
  · intro h q hq
    have hlt : levelInf G y < q := h.trans_lt hq
    obtain ⟨_, ⟨q', hq', rfl⟩, hq'q⟩ := (csInf_lt_iff hbdd hne).1 hlt
    have hq'q' : (q' : ℝ≥0) ≤ q := hq'q.le
    exact hG (show q' ≤ q by exact_mod_cast hq'q') hq'
  · intro h
    refine le_iff_forall_nnrat.2 fun q hq => csInf_le hbdd ⟨q, h q hq, rfl⟩



/-- **Usual-augmentation stopping times of a coupling factor through the marginal.** Let `π : Z → Y` be measurable
and `τ` a stopping time of the usual augmentation of `π⁻¹ 𝓕` under `μ`. Then `τ = τ' ∘ π` `μ`-a.e. for a stopping time
`τ'` of the usual augmentation of `𝓕` under the marginal `μ ∘ π⁻¹`, and every event of the stopped σ-algebra of `τ`
is `μ`-a.e. the preimage of an event of the stopped σ-algebra of `τ'`. -/
theorem exists_factor_stoppingTime_map (hπ : Measurable π) {τ : Z → ℝ≥0}
    (hτ : IsStoppingTime (usualAugmentation (Coupling.filtrationComap 𝓕 hπ) μ) fun ω => (τ ω : WithTop ℝ≥0)) :
    ∃ (τ' : Y → ℝ≥0) (hτ' : IsStoppingTime (usualAugmentation 𝓕 (μ.map π)) fun y => (τ' y : WithTop ℝ≥0)),
      (∀ᵐ ω ∂μ, τ ω = τ' (π ω)) ∧
      ∀ E, MeasurableSet[hτ.measurableSpace] E →
        ∃ E', MeasurableSet[hτ'.measurableSpace] E' ∧ E =ᵐ[μ] π ⁻¹' E' := by
  classical
  set 𝓕' := Coupling.filtrationComap 𝓕 hπ with h𝓕'
  set ν := μ.map π with hν
  have hna : ∀ r, 𝓕 r ⊔ Ito.nullSets ν ≤ mY := fun r => sup_le (𝓕.le r) (Ito.nullSets_le ν)
  -- the sublevel sets of `τ`
  set L : ℚ≥0 → Set Z := fun q => {ω | τ ω ≤ (q : ℝ≥0)} with hL
  have hLua : ∀ q : ℚ≥0, MeasurableSet[usualAugmentation 𝓕' μ q] (L q) := fun q => by
    have h := hτ (q : ℝ≥0)
    simpa only [WithTop.coe_le_coe] using h
  have hLm : ∀ q, MeasurableSet (L q) := fun q => (usualAugmentation 𝓕' μ).le _ _ (hLua q)
  have hK : ∀ q r : ℚ≥0, q < r → ∃ A, MeasurableSet[𝓕 r] A ∧ L q =ᵐ[μ] π ⁻¹' A :=
    fun q r hqr => exists_preimage_of_usualAugmentation hπ (by exact_mod_cast hqr) (hLua q)
  choose! A hAm hAe using hK
  have hAm' : ∀ q r : ℚ≥0, q < r → MeasurableSet (A q r) := fun q r h => 𝓕.le r _ (hAm q r h)
  -- the representatives `D q = A q (q + 1)` and their monotone envelope `G`
  set D : ℚ≥0 → Set Y := fun q => A q (q + 1) with hD
  have hDm : ∀ q, MeasurableSet (D q) := fun q => hAm' q (q + 1) (lt_add_one q)
  have hDe : ∀ q, L q =ᵐ[μ] π ⁻¹' D q := fun q => hAe q (q + 1) (lt_add_one q)
  have hDsub : ∀ p q : ℚ≥0, p ≤ q → (D p \ D q : Set Y) =ᵐ[ν] (∅ : Set Y) := by
    intro p q hpq
    have hLsub : (L p \ L q : Set Z) = ∅ := by
      refine eq_empty_of_forall_notMem fun ω hω => hω.2 ?_
      exact (show τ ω ≤ (p : ℝ≥0) from hω.1).trans (by exact_mod_cast hpq)
    have h1 : π ⁻¹' (D p \ D q) =ᵐ[μ] π ⁻¹' (∅ : Set Y) := by
      rw [preimage_sdiff, preimage_empty, ← hLsub]
      exact ((hDe p).diff (hDe q)).symm
    exact ae_eq_of_preimage_ae_eq hπ ((hDm p).diff (hDm q)) MeasurableSet.empty h1
  set Zc : Set Y := (⋃ q, D q)ᶜ with hZc
  have hZcm : MeasurableSet Zc := (MeasurableSet.iUnion hDm).compl
  have hZc0 : Zc =ᵐ[ν] (∅ : Set Y) := by
    have hcov : (⋃ q, L q : Set Z) = univ := by
      ext ω
      simp only [mem_iUnion, hL, Set.mem_ofPred_eq, mem_univ, iff_true]
      obtain ⟨n, hn⟩ := exists_nat_ge (τ ω)
      exact ⟨n, by exact_mod_cast hn⟩
    have h1 : π ⁻¹' Zc =ᵐ[μ] π ⁻¹' (∅ : Set Y) := by
      rw [hZc, preimage_compl, preimage_iUnion, preimage_empty]
      have h2 : (⋃ q, π ⁻¹' D q : Set Z) =ᵐ[μ] (⋃ q, L q : Set Z) :=
        EventuallyEqSet.countable_iUnion fun q => (hDe q).symm
      rw [hcov] at h2
      have h3 := ae_eq_set_compl_compl.2 h2
      rwa [compl_univ] at h3
    exact ae_eq_of_preimage_ae_eq hπ hZcm MeasurableSet.empty h1
  set G : ℚ≥0 → Set Y := fun q => (⋃ (p : ℚ≥0) (_ : p ≤ q), D p) ∪ Zc with hG
  have hGmono : Monotone G := by
    intro q q' hqq' y hy
    rcases hy with hy | hy
    · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 hy
      exact Or.inl (mem_iUnion₂.2 ⟨p, hp.trans hqq', hyp⟩)
    · exact Or.inr hy
  have hGm : ∀ q, MeasurableSet (G q) := fun q =>
    (MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ => hDm p).union hZcm
  have hGe : ∀ q, G q =ᵐ[ν] D q := by
    intro q
    have h1 : (⋃ (p : ℚ≥0) (_ : p ≤ q), D p : Set Y) =ᵐ[ν] D q := by
      refine ae_eq_set.2 ⟨?_, ?_⟩
      · refine measure_mono_null (t := ⋃ (p : ℚ≥0) (_ : p ≤ q), D p \ D q) ?_ ?_
        · intro y hy
          obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.1 hy.1
          exact mem_iUnion₂.2 ⟨p, hp, hyp, hy.2⟩
        · refine measure_iUnion_null fun p => measure_iUnion_null fun hp => ?_
          exact ae_eq_empty.1 (hDsub p q hp)
      · have : (D q \ ⋃ (p : ℚ≥0) (_ : p ≤ q), D p : Set Y) = ∅ := by
          refine sdiff_eq_empty.2 fun y hy => mem_iUnion₂.2 ⟨q, le_rfl, hy⟩
        rw [this, measure_empty]
    have h2 : (⋃ (p : ℚ≥0) (_ : p ≤ q), D p : Set Y) ∪ Zc =ᵐ[ν] D q ∪ ∅ := h1.union hZc0
    rwa [union_empty] at h2
  have hGcov : ∀ y, ∃ q, y ∈ G q := by
    intro y
    by_cases hy : y ∈ Zc
    · exact ⟨0, Or.inr hy⟩
    · simp only [hZc, mem_compl_iff, not_not, mem_iUnion] at hy
      obtain ⟨q, hq⟩ := hy
      exact ⟨q, Or.inl (mem_iUnion₂.2 ⟨q, le_rfl, hq⟩)⟩
  have hGna : ∀ q r : ℚ≥0, q < r → MeasurableSet[Ito.nullAugmented 𝓕 ν r] (G q) := by
    intro q r hqr
    rw [Ito.nullAugmented_apply]
    have h1 : G q =ᵐ[ν] A q r := (hGe q).trans
      (ae_eq_of_preimage_ae_eq hπ (hDm q) (hAm' q r hqr) ((hDe q).symm.trans (hAe q r hqr)))
    exact measurableSet_of_ae_eq_of_nullSets_le (hna r) le_sup_right (hGm q)
      ((le_sup_left : 𝓕 r ≤ 𝓕 r ⊔ Ito.nullSets ν) _ (hAm q r hqr)) h1
  -- the stopping time `τ'`
  set τ' : Y → ℝ≥0 := levelInf G with hτ'def
  have hτ'le : ∀ y t, τ' y ≤ t ↔ ∀ q : ℚ≥0, t < q → y ∈ G q := fun y t =>
    levelInf_le_iff hGmono (hGcov y) t
  have hτ' : IsStoppingTime (usualAugmentation 𝓕 ν) fun y => (τ' y : WithTop ℝ≥0) := by
    intro t
    have e : {y | (τ' y : WithTop ℝ≥0) ≤ t} = {y | τ' y ≤ t} := by ext y; exact WithTop.coe_le_coe
    rw [e]
    exact measurableSet_usualAugmentation_of_nnrat (f := G) hGmono hGna fun y => hτ'le y t
  -- `τ = τ' ∘ π` almost everywhere
  have hGL : ∀ᵐ ω ∂μ, ∀ q : ℚ≥0, (ω ∈ π ⁻¹' G q ↔ ω ∈ L q) := by
    refine ae_all_iff.2 fun q => ?_
    have h1 : π ⁻¹' G q =ᵐ[μ] L q := (preimage_ae_eq_of_ae_eq hπ (hGe q)).trans (hDe q).symm
    filter_upwards [h1] with ω hω
    exact Iff.of_eq hω
  have hae : ∀ᵐ ω ∂μ, τ ω = τ' (π ω) := by
    filter_upwards [hGL] with ω hω
    refine eq_of_forall_nnrat_le_iff fun q => ?_
    rw [hτ'le]
    constructor
    · intro h q' hq'
      exact (hω q').2 (show τ ω ≤ (q' : ℝ≥0) from h.trans hq'.le)
    · intro h
      refine le_iff_forall_nnrat.2 fun q' hq' => ?_
      exact (hω q').1 (h q' hq')
  refine ⟨τ', hτ', hae, fun E hE => ?_⟩
  -- the stopped σ-algebra
  have hEm : MeasurableSet E := (iSup_le fun t => (usualAugmentation 𝓕' μ).le t) _ hE.1
  set M : ℚ≥0 → Set Z := fun q => E ∩ L q with hM
  have hMua : ∀ q : ℚ≥0, MeasurableSet[usualAugmentation 𝓕' μ q] (M q) := fun q => by
    have h := hE.2 (q : ℝ≥0)
    simpa only [WithTop.coe_le_coe] using h
  have hK' : ∀ q r : ℚ≥0, q < r → ∃ A, MeasurableSet[𝓕 r] A ∧ M q =ᵐ[μ] π ⁻¹' A :=
    fun q r hqr => exists_preimage_of_usualAugmentation hπ (by exact_mod_cast hqr) (hMua q)
  choose! A' hA'm hA'e using hK'
  have hA'm' : ∀ q r : ℚ≥0, q < r → MeasurableSet (A' q r) := fun q r h => 𝓕.le r _ (hA'm q r h)
  have hEU : E = ⋃ n : ℕ, M (n : ℚ≥0) := by
    ext ω
    simp only [mem_iUnion, hM, hL, mem_inter_iff, Set.mem_ofPred_eq, NNRat.cast_natCast]
    refine ⟨fun h => ?_, fun ⟨n, h, _⟩ => h⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (τ ω)
    exact ⟨n, h, hn⟩
  set E' : Set Y := ⋃ n : ℕ, A' (n : ℚ≥0) ((n : ℚ≥0) + 1) with hE'
  have hE'm : MeasurableSet E' := MeasurableSet.iUnion fun n => hA'm' _ _ (lt_add_one _)
  have hEe : E =ᵐ[μ] π ⁻¹' E' := by
    rw [hE', preimage_iUnion]
    conv_lhs => rw [hEU]
    exact EventuallyEqSet.countable_iUnion fun n => hA'e _ _ (lt_add_one _)
  have hE'na : ∀ q r : ℚ≥0, q < r → MeasurableSet[Ito.nullAugmented 𝓕 ν r] (E' ∩ G q) := by
    intro q r hqr
    rw [Ito.nullAugmented_apply]
    have h1 : π ⁻¹' (E' ∩ G q) =ᵐ[μ] π ⁻¹' A' q r := by
      rw [preimage_inter]
      exact (hEe.symm.inter ((preimage_ae_eq_of_ae_eq hπ (hGe q)).trans (hDe q).symm)).trans (hA'e q r hqr)
    exact measurableSet_of_ae_eq_of_nullSets_le (hna r) le_sup_right (hE'm.inter (hGm q))
      ((le_sup_left : 𝓕 r ≤ 𝓕 r ⊔ Ito.nullSets ν) _ (hA'm q r hqr))
      (ae_eq_of_preimage_ae_eq hπ (hE'm.inter (hGm q)) (hA'm' q r hqr) h1)
  have hE'i : ∀ t : ℝ≥0, MeasurableSet[usualAugmentation 𝓕 ν t] (E' ∩ {y | (τ' y : WithTop ℝ≥0) ≤ t}) := by
    intro t
    have e : E' ∩ {y | (τ' y : WithTop ℝ≥0) ≤ t} = E' ∩ {y | τ' y ≤ t} := by
      ext y; exact and_congr_right fun _ => WithTop.coe_le_coe
    rw [e]
    refine measurableSet_usualAugmentation_of_nnrat (f := fun q => E' ∩ G q)
      (fun q q' hqq' => inter_subset_inter_right _ (hGmono hqq')) hE'na fun y => ?_
    simp only [mem_inter_iff, Set.mem_ofPred_eq, hτ'le]
    refine ⟨fun ⟨h1, h2⟩ q hq => ⟨h1, h2 q hq⟩, fun h => ?_⟩
    obtain ⟨q, hq, -⟩ := exists_nnrat_btwn (lt_add_one t)
    exact ⟨(h q hq).1, fun q hq => (h q hq).2⟩
  refine ⟨E', ⟨?_, hE'i⟩, hEe⟩
  have e : E' = ⋃ n : ℕ, E' ∩ {y | (τ' y : WithTop ℝ≥0) ≤ ((n : ℝ≥0) : WithTop ℝ≥0)} := by
    ext y
    simp only [mem_iUnion, mem_inter_iff, Set.mem_ofPred_eq]
    refine ⟨fun h => ?_, fun ⟨n, h, _⟩ => h⟩
    obtain ⟨n, hn⟩ := exists_nat_ge (τ' y)
    exact ⟨n, h, WithTop.coe_le_coe.2 hn⟩
  rw [e]
  exact MeasurableSet.iUnion fun n =>
    le_iSup (fun t => (usualAugmentation 𝓕 ν t : MeasurableSpace Y)) (n : ℝ≥0) _ (hE'i n)

end Factor

end InteractingSLE.ZhanGT4.A1Core
