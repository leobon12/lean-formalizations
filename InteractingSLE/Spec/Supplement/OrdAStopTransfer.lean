/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.StoppedK2Kernel

/-!
# Announcing stops that see initial data: the transfer to the regular conditional law

Packet PROVE-T15-ASTOP. Theorem 1.5's leaf 3 stops each continuation at its first new contact with the retained
union `A = η₁[0,u] ∪ η₂[0,r]` only (Lemma G7, supplement p. 497: real contacts are allowed). In the continuation's
chart this is the first positive time at which the chart trace meets the closed chart image `I_A ⊂ ℝ` of `A`. The
stopped K2 (`Restart.StoppedK2.ae_isStoppedHullCoupling_k`) asks for stopping times `σₙ ↑ V` of the driving
filtration of the continuation killed at `V`. When an end point of `I_A` is not a genuine jump of the chart word it is
not a force coordinate, so the driving process does not see it, and in general the A-stop is not predictable in the
driving filtration (whether a real contact near that end point is a contact with `A` is decided by a coordinate the
driving process never reads). The stopped K2 conditions on an initial σ-algebra `𝒢` that contains the chart word and
`I_A`; under the regular conditional law `ν = condExpKernel P 𝒢 ω₀` every `𝒢`-measurable datum is almost surely
constant. So it suffices that the `σₙ` be stopping times of the driving filtration **enlarged at time `0` by the
σ-algebra of a `𝒢`-measurable real code `e`** (`supConst`): this file proves that such stopping times are, for almost
every `ω₀`, stopping times of the `ν`-driving filtration of every version (`ae_isStoppingTime_of_agree_sup`, the
analogue of `Restart.StoppedK2.ae_isStoppingTime_of_agree`).

## Main results

* `supConst`: the filtration `t ↦ 𝓕 t ⊔ 𝒥`;
* `ae_map_condExpKernel_eq_dirac`: the regular conditional law of a `𝒢`-measurable real code is almost surely the
  Dirac mass at its value;
* `exists_ae_eq_of_measurableSet_sup_comap`: if the law of `e` under `ν` is a Dirac mass, every event of
  `m ⊔ σ(e)` is `ν`-almost surely an event of `m`;
* **`ae_isStoppingTime_of_agree_sup`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdAStop

/-! ### The filtration enlarged at time `0` -/

section SupConst

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The filtration enlarged at time `0`** by a sub-σ-algebra `𝒥`: `t ↦ 𝓕 t ⊔ 𝒥`. -/
def supConst (𝓕 : Filtration ℝ≥0 mΩ) (𝒥 : MeasurableSpace Ω) (h𝒥 : 𝒥 ≤ mΩ) : Filtration ℝ≥0 mΩ where
  seq t := 𝓕 t ⊔ 𝒥
  mono' _ _ hst := sup_le_sup_right (𝓕.mono hst) _
  le' t := sup_le (𝓕.le t) h𝒥

theorem supConst_apply (𝓕 : Filtration ℝ≥0 mΩ) (𝒥 : MeasurableSpace Ω) (h𝒥 : 𝒥 ≤ mΩ) (t : ℝ≥0) :
    supConst 𝓕 𝒥 h𝒥 t = 𝓕 t ⊔ 𝒥 := rfl

theorem le_supConst (𝓕 : Filtration ℝ≥0 mΩ) (𝒥 : MeasurableSpace Ω) (h𝒥 : 𝒥 ≤ mΩ) : 𝓕 ≤ supConst 𝓕 𝒥 h𝒥 :=
  fun _ => le_sup_left

theorem le_supConst_const (𝓕 : Filtration ℝ≥0 mΩ) (𝒥 : MeasurableSpace Ω) (h𝒥 : 𝒥 ≤ mΩ) (t : ℝ≥0) :
    𝒥 ≤ supConst 𝓕 𝒥 h𝒥 t :=
  le_sup_right

end SupConst

/-! ### Initial codes under the regular conditional law -/

section Dirac

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The regular conditional law of a `𝒢`-measurable real code is the Dirac mass at its value**, almost surely. -/
theorem ae_map_condExpKernel_eq_dirac (h𝒢 : 𝒢 ≤ mΩ) {e : Ω → ℝ} (he : Measurable[𝒢] e) :
    ∀ᵐ ω₀ ∂P, (condExpKernel P 𝒢 ω₀).map e = Measure.dirac (e ω₀) := by
  have hall : ∀ᵐ ω₀ ∂P, ∀ q : ℚ, condExpKernel P 𝒢 ω₀ (e ⁻¹' Iic (q : ℝ)) =
      (e ⁻¹' Iic (q : ℝ)).indicator 1 ω₀ :=
    ae_all_iff.2 fun q => Sec7.Aux122Disint.ae_condExpKernel_apply_eq_indicator h𝒢 (he measurableSet_Iic)
  have hem : Measurable e := he.mono h𝒢 le_rfl
  filter_upwards [hall] with ω₀ hω₀
  refine ext_of_generate_finite _ (BorelSpace.measurable_eq.trans Real.borel_eq_generateFrom_Iic_rat)
    Real.isPiSystem_Iic_rat (fun s hs => ?_) ?_
  · obtain ⟨q, hq⟩ := mem_iUnion.1 hs
    rw [mem_singleton_iff] at hq
    subst hq
    rw [Measure.map_apply hem measurableSet_Iic, hω₀ q, Measure.dirac_apply' _ measurableSet_Iic]
    by_cases h : e ω₀ ≤ q
    · rw [indicator_of_mem (show ω₀ ∈ e ⁻¹' Iic (q : ℝ) from h),
        indicator_of_mem (show e ω₀ ∈ Iic (q : ℝ) from h)]
      rfl
    · rw [indicator_of_notMem (show ω₀ ∉ e ⁻¹' Iic (q : ℝ) from h),
        indicator_of_notMem (show e ω₀ ∉ Iic (q : ℝ) from h)]
  · rw [Measure.map_apply hem MeasurableSet.univ, preimage_univ, measure_univ, measure_univ]

end Dirac

section Reduce

variable {Ω : Type*}

/-- **Events of `m ⊔ σ(e)` are almost surely events of `m`** under a law for which `e` is almost surely constant. -/
theorem exists_ae_eq_of_measurableSet_sup_comap {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {ν : Measure Ω} {e : Ω → ℝ}
    (hem : Measurable e) {c : ℝ} (hν : ν.map e = Measure.dirac c) {K : Set Ω}
    (hK : MeasurableSet[m ⊔ MeasurableSpace.comap e inferInstance] K) :
    ∃ K' : Set Ω, MeasurableSet[m] K' ∧ K =ᵐ[ν] K' := by
  replace hK := MeasurableSpace.measurableSet_sup.1 hK
  induction hK with
  | basic s hs =>
    rcases hs with hs | hs
    · exact ⟨s, hs, EventuallyEq.rfl⟩
    · obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hs
      have hmap : ∀ C : Set ℝ, MeasurableSet C → ν (e ⁻¹' C) = Measure.dirac c C := fun C hC => by
        rw [← Measure.map_apply hem hC, hν]
      by_cases hc : c ∈ B
      · refine ⟨univ, @MeasurableSet.univ Ω m, ae_eq_univ.2 ?_⟩
        rw [← preimage_compl, hmap _ hB.compl, Measure.dirac_apply' _ hB.compl,
          indicator_of_notMem (show c ∉ Bᶜ from fun h => h hc)]
      · refine ⟨∅, @MeasurableSet.empty Ω m, ae_eq_empty.2 ?_⟩
        rw [hmap _ hB, Measure.dirac_apply' _ hB, indicator_of_notMem hc]
  | empty => exact ⟨∅, @MeasurableSet.empty Ω m, EventuallyEq.rfl⟩
  | compl s _ ih =>
    obtain ⟨K', hK', hsK'⟩ := ih
    exact ⟨K'ᶜ, hK'.compl, hsK'.compl⟩
  | iUnion f _ ih =>
    choose K' hK' hfK' using ih
    exact ⟨⋃ i, K' i, MeasurableSet.iUnion hK', EventuallyEqSet.countable_iUnion hfK'⟩

end Reduce

/-! ### Stopping times of the enlarged killed driving filtration under the conditional law -/

section Stop

open Ito Coupling Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Restart.StoppedK2

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {nL nR : ℕ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **The killed driving filtration enlarged at time `0` by a real code `e`**, usual augmentation under `P`. -/
abbrev drivingSupCode (P : Measure Ω) (hXP : IsMeasurableKilledDriving W VL VR ζ) {e : Ω → ℝ}
    (hem : Measurable e) : Filtration ℝ≥0 mΩ :=
  usualAugmentation (supConst (killedDrivingFiltration hXP) (MeasurableSpace.comap e inferInstance)
    hem.comap_le) P

theorem drivingFiltration_le_drivingSupCode (P : Measure Ω) (hXP : IsMeasurableKilledDriving W VL VR ζ)
    {e : Ω → ℝ} (hem : Measurable e) : drivingFiltration P hXP ≤ drivingSupCode P hXP hem :=
  usualAugmentation_mono (le_supConst _ _ _) P

variable {P : Measure Ω} [StandardBorelSpace Ω] [IsProbabilityMeasure P]

/-- **Stopping times of the killed driving filtration enlarged by a `𝒢`-measurable code transfer to the killed
driving filtration of versions** under `ν = condExpKernel P 𝒢 ω₀`, for almost every `ω₀`
(`Restart.StoppedK2.ae_isStoppingTime_of_agree` for the enlarged filtration: under `ν` the code is almost surely
constant, `ae_map_condExpKernel_eq_dirac`, so the enlargement only adds `ν`-trivial events,
`exists_ae_eq_of_measurableSet_sup_comap`). -/
theorem ae_isStoppingTime_of_agree_sup (h𝒢 : 𝒢 ≤ mΩ) {e : Ω → ℝ} (he : Measurable[𝒢] e)
    (hXP : IsMeasurableKilledDriving W VL VR ζ) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingSupCode P hXP (he.mono h𝒢 le_rfl)) σ) :
    ∀ᵐ ω₀ ∂P, ∀ (W' : ℝ≥0 → Ω → ℝ) (VL' : Fin nL → ℝ≥0 → Ω → ℝ) (VR' : Fin nR → ℝ≥0 → Ω → ℝ)
      (hX' : IsMeasurableKilledDriving W' VL' VR' ζ),
      (∀ᵐ ω ∂(condExpKernel P 𝒢 ω₀), ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W' t ω = W t ω ∧
        (∀ i, VL' i t ω = VL i t ω) ∧ ∀ j, VR' j t ω = VR j t ω) →
      IsStoppingTime (drivingFiltration (condExpKernel P 𝒢 ω₀) hX') σ := by
  have hem : Measurable e := he.mono h𝒢 le_rfl
  set 𝓚 := killedDrivingFiltration hXP with h𝓚
  set 𝓚J := supConst 𝓚 (MeasurableSpace.comap e inferInstance) hem.comap_le with h𝓚J
  have hver : ∀ q s : ℚ, ∃ K : Set Ω, (q : ℝ).toNNReal < (s : ℝ).toNNReal →
      MeasurableSet[𝓚J (s : ℝ).toNNReal] K ∧
        {ω | σ ω ≤ (((q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} =ᵐ[P] K := by
    intro q s
    by_cases hqs : (q : ℝ).toNNReal < (s : ℝ).toNNReal
    · have h1 := usualAugmentation_le_nullAugmented (P := P) 𝓚J hqs _ (hσ (q : ℝ).toNNReal)
      obtain ⟨K, hK, hEK⟩ := exists_ae_eq_of_measurableSet_nullAugmented h1
      exact ⟨K, fun _ => ⟨hK, hEK⟩⟩
    · exact ⟨∅, fun h => absurd h hqs⟩
  choose K hK using hver
  have hall : ∀ᵐ ω₀ ∂P, ∀ q s : ℚ, (q : ℝ).toNNReal < (s : ℝ).toNNReal →
      {ω | σ ω ≤ (((q : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} =ᵐ[condExpKernel P 𝒢 ω₀] K q s := by
    refine ae_all_iff.2 fun q => ae_all_iff.2 fun s => ?_
    by_cases hqs : (q : ℝ).toNNReal < (s : ℝ).toNNReal
    · have h := Sec7.Aux122Disint.ae_ae_condExpKernel (P := P) h𝒢 (hK q s hqs).2
      filter_upwards [h] with ω₀ hω₀ _ using hω₀
    · exact Eventually.of_forall fun _ h => absurd h hqs
  filter_upwards [hall, ae_map_condExpKernel_eq_dirac (P := P) h𝒢 he] with ω₀ hω₀ hdir W' VL' VR' hX' hag
  set ν := condExpKernel P 𝒢 ω₀ with hν
  have hsym : ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → W t ω = W' t ω ∧
      (∀ i, VL i t ω = VL' i t ω) ∧ ∀ j, VR j t ω = VR' j t ω := by
    filter_upwards [hag] with ω hω t ht
    obtain ⟨e1, e2, e3⟩ := hω t ht
    exact ⟨e1.symm, fun i => (e2 i).symm, fun j => (e3 j).symm⟩
  have hle := fun s => nullAugmented_le_of_agree (adaptedBefore_killedDriving_W hX')
    (fun i => adaptedBefore_killedDriving_VL hX' i) (fun j => adaptedBefore_killedDriving_VR hX' j) hXP hsym s
  intro t
  show MeasurableSet[usualAugmentation (killedDrivingFiltration hX') ν t] _
  rw [usualAugmentation_apply]
  refine MeasurableSpace.measurableSet_iInf.2 fun u => MeasurableSpace.measurableSet_iInf.2 fun htu => ?_
  rw [setOf_le_eq_iInter σ htu]
  refine MeasurableSet.iInter fun q => ?_
  have hq0 : (0 : ℝ) ≤ q.1 := t.coe_nonneg.trans q.2.1.le
  obtain ⟨s, hs1, hs2⟩ := exists_rat_btwn q.2.2
  have hs0 : (0 : ℝ) ≤ s := hq0.trans hs1.le
  have hqs : (q.1 : ℝ).toNNReal < (s : ℝ).toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0, Real.coe_toNNReal _ hs0]; exact hs1
  have hsu : (s : ℝ).toNNReal ≤ u := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs0]; exact hs2.le
  obtain ⟨K₀, hK₀, hKK₀⟩ := exists_ae_eq_of_measurableSet_sup_comap (m := 𝓚 (s : ℝ).toNNReal) hem hdir (hK q.1 s hqs).1
  obtain ⟨K', hK', hKK'⟩ := hle _ _ (le_nullAugmented 𝓚 ν _ _ hK₀)
  have hEm : MeasurableSet {ω | σ ω ≤ (((q.1 : ℝ).toNNReal : ℝ≥0) : WithTop ℝ≥0)} :=
    (drivingSupCode P hXP hem).le _ _ (hσ _)
  have h1 := Coupling.measurableSet_nullAugmented_of_ae_eq (𝓕 := killedDrivingFiltration hX') (P := ν) hEm hK'
    (((hω₀ q.1 s hqs).trans hKK₀).trans hKK')
  exact (nullAugmented (killedDrivingFiltration hX') ν).mono hsu _ h1

end Stop

end InteractingSLE.RLC.OrdAStop
