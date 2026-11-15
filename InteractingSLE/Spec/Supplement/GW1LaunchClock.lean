/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1WalkExitParam
import InteractingSLE.Spec.Supplement.GW2LaterChain

/-! # GW1 launch clocks: first contacts and a measurable original counterflow -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW1LaunchClock

theorem firstTipTime_mono {c : Chart} {W : ℝ≥0 → ℝ} {A B : Set ℂ}
    (h : A ⊆ B) : firstTipTime c W B ≤ firstTipTime c W A := by
  refine le_iInf fun t => le_iInf fun ht => ?_
  obtain ⟨z, hz, htip⟩ := ht
  exact iInf₂_le t ⟨z, h hz, htip⟩

theorem firstTipTime_eq_top_of_no_tip {c : Chart} {W : ℝ≥0 → ℝ} {A : Set ℂ}
    (h : ∀ t z, c.tipAt W t z → z ∉ A) : firstTipTime c W A = ⊤ := by
  apply top_unique
  refine le_iInf fun t => le_iInf fun ht => ?_
  obtain ⟨z, hz, htip⟩ := ht
  exact False.elim (h t z htip hz)

/-- The physical target `0` is reached only at infinite counterflow capacity.
This follows from the existing inversion-tip formula, including at time zero. -/
theorem firstTipTime_root_eq_top {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0) :
    firstTipTime infinitySourceChart W {(0 : ℂ)} = ⊤ := by
  apply firstTipTime_eq_top_of_no_tip
  intro t z ht hz
  have hm : z ∈ infinitySourceChart.tipSet W ⊤ := ⟨t, le_top, ht⟩
  rw [CounterflowRange.tipSet_infinitySourceChart_top hγ hW hW0] at hm
  obtain ⟨r, hr, he⟩ := hm
  rw [mem_singleton_iff.1 hz] at he
  exact hr (inv_eq_zero.1 (neg_eq_zero.1 he.symm))

/-- Killing after the lifetime supplies measurable coordinates without changing
any sample with infinite lifetime. The original driver need only be adapted before it. -/
theorem exists_measurable_counterflow_version {κ : ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∃ V : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (V t)) ∧
      IsCenteredCounterflowDriver κ P h V ζ ∧
      ∀ᵐ ω ∂P, (fun t => V t ω) = (fun t => W t ω) := by
  obtain ⟨b, J, h', hb, ht, hfl⟩ := hcf
  have hfl' := hfl
  obtain ⟨_, 𝓕, _, _, _, _, hC⟩ := hfl'
  let V := Girsanov.killed ζ W
  have hVm : ∀ t, Measurable (V t) := fun t =>
    (Girsanov.measurable_killed hC.1.2.1 t).mono (𝓕.le t) le_rfl
  have he : ∀ᵐ ω ∂P, (fun t => V t ω) = (fun t => W t ω) := by
    filter_upwards [hζ] with ω hω
    funext t
    exact Girsanov.killed_of_lt (by rw [hω]; exact ENNReal.coe_lt_top)
  refine ⟨V, hVm, ⟨b, J, h', hb, ht, ?_⟩, he⟩
  apply StagedReg.isFlowLineDriver_congr_ae hfl hVm
  filter_upwards [he] with ω hω
  exact ⟨congrFun hω 0, fun t _ => congrFun hω t⟩

/-- Theorem 1.3 gives the original counterflow's pathwise regularity on one conull set. -/
theorem ae_counterflow_regular (hT13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) :
    ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧
      ∃ γ : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ γ ∧
        Tendsto (fun t => ‖γ t‖) atTop atTop := by
  obtain ⟨b, J, h', _, _, hfl⟩ := hcf
  filter_upwards [GW2aSingle.ae_chosenTrace hT13 (by positivity : 0 < 16 / κ) hfl,
    InteractingSLE.Supp8.GB6.ae_driver_zero_continuousOn hfl, hζ] with ω hγ hW hζω
  rw [hζω] at hγ hW
  exact ⟨continuousOn_univ.1 (hW.2.mono fun _ _ => ENNReal.coe_lt_top), hW.1,
    ⟨GW2aSingle.chosenTrace W ζ ω, hγ.1, hγ.2 rfl⟩⟩

end InteractingSLE.Theorem14.GW1LaunchClock
