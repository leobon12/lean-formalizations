/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.TwoMarkRegular5Limits
import InteractingSLE.Spec.Sec5.TwoMarkRetarget

/-!
# The stopped image barrier from a completed trace

Closing only terminal state values removes the terminal state continuity premise
from the two-mark left-ray barrier. The trace itself is unchanged.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.TwoMark.Regular5

/-- Adaptedness before the horizon only sees values strictly before it. -/
theorem adaptedBefore_endpointClose {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ} {τ : Ω → ℝ≥0∞} {X : ℝ≥0 → Ω → ℝ}
    (hX : AdaptedBefore 𝓕 τ X) :
    AdaptedBefore 𝓕 τ (fun t ω => endpointClose (τ ω) (X · ω) t) := by
  intro t A hA
  have heq : {ω | (t : ℝ≥0∞) < τ ω ∧ endpointClose (τ ω) (X · ω) t ∈ A} =
      {ω | (t : ℝ≥0∞) < τ ω ∧ X t ω ∈ A} := by
    ext ω
    by_cases ht : (t : ℝ≥0∞) < τ ω
    · simp only [mem_ofPred_eq, ht, true_and, endpointClose_of_lt ht]
    · simp only [mem_ofPred_eq, ht, false_and]
  rw [heq]
  exact hX t A hA

/-- Closing terminal state values preserves the same local stochastic evolution. -/
theorem isSLEEvolutionUpTo_endpointClose {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {a : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞}
    (hE : Sec2.IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕 W VL VR B τ) :
    Sec2.IsSLEEvolutionUpTo a xL xR ρL ρR P 𝓕
      (fun t ω => endpointClose (τ ω) (W · ω) t)
      (fun i t ω => endpointClose (τ ω) (VL i · ω) t)
      (fun j t ω => endpointClose (τ ω) (VR j · ω) t) B τ := by
  refine ⟨hE.brownian, adaptedBefore_endpointClose hE.adapted_W,
    fun i => adaptedBefore_endpointClose (hE.adapted_VL i),
    fun j => adaptedBefore_endpointClose (hE.adapted_VR j), ?_⟩
  filter_upwards [hE.ae_path] with ω hp
  exact Sec2.Assembly2.isSLEPathUpTo_congr hp (endpointClose_zero _ _)
    (fun _ => endpointClose_zero _ _) (fun _ => endpointClose_zero _ _)
    (fun _ ht => endpointClose_of_lt ht) (fun _ ht _ => endpointClose_of_lt ht)
    (fun _ ht _ => endpointClose_of_lt ht) (fun _ _ => rfl)

/-- A completed trace makes the closed local state continuous through every finite horizon. -/
theorem continuousOn_state_endpointClose {a : ℝ} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {w b : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hp : Sec2.IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w τ η) {s : ℝ≥0} (hs : (s : ℝ≥0∞) = τ) :
    ContinuousOn (fun t => (endpointClose τ w t,
      fun i => endpointClose τ (vL i) t, fun j => endpointClose τ (vR j) t)) (Iic s) := by
  have hw (hpos : 0 < s) : ∃ c : ℝ, Tendsto w (𝓝[<] s) (𝓝 c) :=
    Restart.RetEnd.exists_tendsto_driver_of_isGeneratingTrace (hs.symm ▸ hη)
      (hs.symm ▸ hp.continuousOn_w) hp.w_zero hpos
  have hlimits (hpos : 0 < s) := exists_force_limits_of_driver_limit hp hs (hw hpos)
  exact (continuousOn_endpointClose hp.continuousOn_w hs hw).prodMk
    ((continuousOn_pi.2 fun i => continuousOn_endpointClose (hp.continuousOn_vL i) hs
      (fun hpos => (hlimits hpos).1 i)).prodMk
    (continuousOn_pi.2 fun j => continuousOn_endpointClose (hp.continuousOn_vR j) hs
      (fun hpos => (hlimits hpos).2 j)))

/-- The stopped two-mark image barrier, without a terminal state continuity assumption. -/
theorem ae_avoid_left_ray_of_completed_trace {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {κ a b r : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) (ha : 0 < a) (hab : a < b)
    (hr : r ≤ κ / 2 - 4)
    {xR ρR : Fin 0 → ℝ} {W B : ℝ≥0 → Ω → ℝ}
    {VL : Fin 2 → ℝ≥0 → Ω → ℝ} {VR : Fin 0 → ℝ≥0 → Ω → ℝ}
    {e : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} {η : Ω → ℝ≥0 → ℂ}
    (hE : Sec2.IsSLEEvolutionUpTo κ ![-1, Sec7.targetChangeReal a b] xR
      ![κ - 6, -r] ρR P 𝓕 W VL VR B e)
    (hW : ∀ ω, ContinuousOn (W · ω) {t | (t : ℝ≥0∞) < e ω})
    (hL : ∀ i ω, ContinuousOn (VL i · ω) {t | (t : ℝ≥0∞) < e ω})
    (hT : Coupling.IsAnnouncingSeq 𝓕 P e T)
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (W · ω) (e ω) (η ω))
    (hinj : ∀ᵐ ω ∂P, InjOn (η ω) {t | (t : ℝ≥0∞) ≤ e ω}) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ e ω →
      ∀ y < Sec7.targetChangeReal a b, η ω t ≠ (y : ℂ) := by
  have hg : ∀ᵐ ω ∂P, IsGeneratingTrace
      (endpointClose (e ω) (W · ω)) (e ω) (η ω) := by
    filter_upwards [hη] with ω hg
    exact Sec7.IsGeneratingTrace.congr_lt hg (fun _ ht => endpointClose_of_lt ht)
  have hc : ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) = e ω →
      ContinuousOn (fun t => (endpointClose (e ω) (W · ω) t,
        fun i => endpointClose (e ω) (VL i · ω) t,
        fun j => endpointClose (e ω) (VR j · ω) t)) (Iic s) := by
    filter_upwards [hE.ae_path, hη] with ω hp hg s hs
    exact continuousOn_state_endpointClose hp hg hs
  exact TwoMark.ae_avoid_left_ray hκ hκ4 ha hab hr (isSLEEvolutionUpTo_endpointClose hE)
    (fun ω => continuousOn_endpointClose_before (hW ω))
    (fun i ω => continuousOn_endpointClose_before (hL i ω)) hT hg hinj hc

end InteractingSLE.Sec5.TwoMark.Regular5
