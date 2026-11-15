/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafMartMSpace

/-!
# Douglas separation: the sole standard theorem input

The named input below is the relative annihilator form of Douglas's theorem,
Revuz--Yor, Chapter V, Theorem (4.4), printed p. 210. It is a statement about
linear subspaces of L¹ and bounded changes of probability measure. It mentions
no filtration, stochastic process, SLE, or continuity. The following lemmas
prove the stochastic consequences needed here using the landed L¹ closure.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WFS

/-- The relative separation assertion used in the proof of [RY99] V.(4.4),
p. 210. If every bounded probability perturbation preserving a linear space
also preserves the mean of `Z`, then `Z` is in that space's L¹ closure.
This standard functional-analysis theorem is the one unproved input here. -/
def DouglasL1SeparationStatement : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (C : Submodule ℝ (Ω → ℝ)), (∀ f ∈ C, Integrable f P) → (fun _ => (1 : ℝ)) ∈ C →
    ∀ Z : Ω → ℝ, Integrable Z P →
      (∀ (Q : Measure Ω) [IsProbabilityMeasure Q], Q ≤ (2 : ℝ≥0∞) • P →
        (∀ f ∈ C, (∫ ω, f ω ∂Q) = ∫ ω, f ω ∂P) →
          (∫ ω, Z ω ∂Q) = ∫ ω, Z ω ∂P) →
      ∀ ε : ℝ, 0 < ε → ∃ Y : Ω → ℝ, Y ∈ C ∧ (∫ ω, ‖Y ω - Z ω‖ ∂P) < ε

/-- A bounded change of measure preserving the means of the closed space
preserves every continuous martingale of the original filtration. -/
theorem martingale_of_continuousClosedSpace_means
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P Q : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    {𝓓 : Filtration ℝ≥0 mΩ} (hQP : Q ≤ (2 : ℝ≥0∞) • P)
    (hmeans : ∀ Z ∈ continuousClosedSpace 𝓓 P, (∫ ω, Z ω ∂Q) = ∫ ω, Z ω ∂P)
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M 𝓓 P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => M t ω)) : Martingale M 𝓓 Q := by
  have hi (t : ℝ≥0) : Integrable (M t) Q :=
    ((hM.integrable t).smul_measure (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).mono_measure hQP
  refine ⟨hM.stronglyAdapted, fun s t hst => ?_⟩
  apply EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (𝓓.le s) (hi t)
    (fun A _ _ => (hi s).integrableOn) (fun A hA _ => ?_)
    (hM.stronglyAdapted s).aestronglyMeasurable
  have hAm := 𝓓.le s _ hA
  have he := hmeans (A.indicator (M t - M s))
    (indicator_martingale_increment_mem_continuousClosedSpace hM hc hst hA)
  rw [integral_indicator hAm, integral_indicator hAm] at he
  simp only [Pi.sub_apply] at he
  rw [integral_sub (hi t).integrableOn (hi s).integrableOn,
    integral_sub (hM.integrable t).integrableOn (hM.integrable s).integrableOn,
    ← hM.setIntegral_eq hst hA, sub_self] at he
  exact (sub_eq_zero.1 he).symm

/-- Douglas separation plus the proved L¹ closure constructs a continuous
closed process once preservation of the closed-space means forces the mean
of the desired terminal variable to be preserved. -/
theorem mem_continuousClosedSpace_of_douglas
    (hDouglas : DouglasL1SeparationStatement.{u})
    {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓓 : Filtration ℝ≥0 mΩ) (hn : ∀ t, nullSigma P ≤ 𝓓 t)
    {Z : Ω → ℝ} (hZi : Integrable Z P)
    (hinv : ∀ (Q : Measure Ω) [IsProbabilityMeasure Q], Q ≤ (2 : ℝ≥0∞) • P →
      (∀ f ∈ continuousClosedSpace 𝓓 P, (∫ ω, f ω ∂Q) = ∫ ω, f ω ∂P) →
        (∫ ω, Z ω ∂Q) = ∫ ω, Z ω ∂P) :
    Z ∈ continuousClosedSpace 𝓓 P := by
  refine ⟨hZi, exists_continuous_closed_process_of_L1_approx 𝓓 hn hZi ?_⟩
  intro ε hε
  obtain ⟨Y, hY, he⟩ := hDouglas P (continuousClosedSpace 𝓓 P)
    (fun _ h => h.1) (const_mem_continuousClosedSpace 𝓓 1) Z hZi hinv ε hε
  exact ⟨Y, hY.1, he, hY.2⟩

end InteractingSLE.WFS
