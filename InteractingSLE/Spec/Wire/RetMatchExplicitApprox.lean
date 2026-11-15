/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.RetMatchExplicitDiagonal

/-!
# Raw approximating times eventually below an announced time

Approximate the augmented announcing times by raw upper-dyadic versions. The
summable-error diagonal is eventually strictly below the announced time a.s.
The dyadic error bound proves convergence to that time, including infinity.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.RetMatchExplicit

/-- An augmented announcement admits raw approximating times converging to
its limit and eventually strictly below that limit, almost surely. -/
theorem exists_raw_approximation_of_announcingSeq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    {A : ℕ → Ω → ℝ≥0}
    (hA : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P V A) :
    ∃ R : ℕ → Ω → WithTop ℝ≥0, (∀ n, IsStoppingTime 𝓕 (R n)) ∧
      ∀ᵐ ω ∂P, (∀ᶠ n in atTop, (R n ω : ℝ≥0∞) < V ω) ∧
        Tendsto (fun n => (R n ω : ℝ≥0∞)) atTop (𝓝 (V ω)) := by
  have hex : ∀ n m, ∃ R : Ω → WithTop ℝ≥0, IsStoppingTime 𝓕 R ∧
      ∀ᵐ ω ∂P, R ω = (dyadicUp m (A n ω) : WithTop ℝ≥0) :=
    fun n m => exists_raw_dyadicApprox (hA.1 n) m
  choose R hR he using hex
  have hRm : ∀ n m, Measurable fun ω => (R n m ω : ℝ≥0∞) :=
    fun n m => (hR n m).measurable'
  let E : ℕ → ℕ → Set Ω := fun n m => {ω | V ω ≤ (R n m ω : ℝ≥0∞)}
  have hEm : ∀ n m, MeasurableSet (E n m) := fun n m =>
    measurableSet_le hVm (hRm n m)
  have hrow : ∀ n, ∀ᵐ ω ∂P, ∀ᶠ m in atTop, ω ∉ E n m := by
    intro n
    filter_upwards [ae_all_iff.2 (he n), hA.2.2.1 n] with ω heω hltω
    have hc : Tendsto (fun m => (dyadicUp m (A n ω) : ℝ≥0∞)) atTop
        (𝓝 (A n ω : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.tendsto (A n ω)).comp
        ((tendsto_dyadicUp (A n ω)).mono_right nhdsWithin_le_nhds)
    filter_upwards [hc.eventually (Iio_mem_nhds hltω)] with m hm
    exact not_le_of_gt ((congrArg (fun x : WithTop ℝ≥0 => (x : ℝ≥0∞))
      (heω m)).trans_lt hm)
  obtain ⟨j, hj, hjgood⟩ := exists_diagonal_eventually_notMem hEm hrow
  have heall : ∀ᵐ ω ∂P, ∀ n m, R n m ω = (dyadicUp m (A n ω) : WithTop ℝ≥0) :=
    ae_all_iff.2 fun n => ae_all_iff.2 (he n)
  have herr : Tendsto (fun n : ℕ => (1 / 2 ^ n : ℝ≥0)) atTop (𝓝 0) := by
    simp_rw [one_div, ← inv_pow]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have herrE : Tendsto (fun n : ℕ => ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) :=
    (ENNReal.continuous_coe.tendsto 0).comp herr
  refine ⟨fun n => R n (j n), fun n => hR n (j n), ?_⟩
  filter_upwards [hjgood, heall, Restart.RetAux79.ae_tendsto_of_isAnnouncingSeq hA]
    with ω hgood heω hlim
  refine ⟨hgood.mono fun n hn => lt_of_not_ge hn, ?_⟩
  have hup : Tendsto (fun n => (A n ω : ℝ≥0∞) + ((1 / 2 ^ n : ℝ≥0) : ℝ≥0∞))
      atTop (𝓝 (V ω)) := by
    simpa only [add_zero] using hlim.add herrE
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlim hup
  · intro n
    exact (ENNReal.coe_le_coe.2 (lt_dyadicUp (j n) (A n ω)).le).trans_eq
      (congrArg (fun x : WithTop ℝ≥0 => (x : ℝ≥0∞)) (heω n (j n))).symm
  · intro n
    have hbound := (dyadicUp_antitone (A n ω) (hj n)).trans (dyadicUp_le_add n (A n ω))
    exact ((congrArg (fun x : WithTop ℝ≥0 => (x : ℝ≥0∞)) (heω n (j n))).trans_le
      (ENNReal.coe_le_coe.2 hbound)).trans_eq (ENNReal.coe_add _ _)

end InteractingSLE.Wire.RetMatchExplicit
