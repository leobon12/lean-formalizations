/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenLaw
import InteractingSLE.WangWu.ImgChartConstDyadic

/-!
# Marked kernels at deterministic forward times suffice

PROVE-CROSSCOND-GEN. Apply the existing upper-dyadic passage to a random inverse
relative clock. In particular no Gaussian kernel at that random time is assumed.
The exact remaining hypotheses are measurability of the censored marked pieces
and convergence of the forward kernels on protected tests. The limiting candidate's
integrability follows from the bounded kernels rather than being an extra input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.Gen

open WangWu.ChartConst

/-- Forward deterministic kernels pass to the raw relative filtration if that
filtration can be read from the censored forward records along the inverse clock.
The marked σ-algebras need not be monotone. -/
theorem ae_condExp_eq_on_of_forward_kernels
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {E : Set Ω} (hE : MeasurableSet[m] E)
    {X G : Ω → ℂ} (hX : Integrable X P) (hXb : ∀ᵐ ω ∂P, ‖X ω‖ ≤ 1)
    (hG : Measurable[m] (E.indicator G))
    (𝓜 : ℕ → ℕ → MeasurableSpace Ω) (h𝓜 : ∀ n k, 𝓜 n k ≤ mΩ)
    {Av : ℝ≥0 → Set Ω} {F : ℝ≥0 → Ω → ℂ}
    (hFb : ∀ q ω, ω ∈ Av q → ‖F q ω‖ ≤ 1)
    (hdet : ∀ n k, ∀ᵐ ω ∂P, ω ∈ Av (dyq n k) →
      P[X | 𝓜 n k] ω = F (dyq n k) ω)
    {τ : Ω → ℝ≥0} (hτ : Measurable[mΩ] τ)
    (hread : ∀ B, MeasurableSet[m] B → ∀ n k, ∃ C, MeasurableSet[𝓜 n k] C ∧
      C =ᵐ[P] (B ∩ E ∩ {ω | dyIdx n (τ ω) = k} ∩ Av (dyq n k)))
    (hlim : ∀ᵐ ω ∂P, ω ∈ E → (∀ᶠ n in atTop, ω ∈ Av (dyF n (τ ω))) ∧
      Tendsto (fun n => F (dyF n (τ ω)) ω) atTop (𝓝 (G ω))) :
    ∀ᵐ ω ∂P, ω ∈ E → P[X | m] ω = G ω := by
  have hGi : Integrable (E.indicator G) P := by
    refine Integrable.of_bound (hG.mono hm le_rfl).aestronglyMeasurable 1 ?_
    filter_upwards [hlim] with ω hω
    by_cases hωE : ω ∈ E
    · rw [indicator_of_mem hωE]
      obtain ⟨hev, ht⟩ := hω hωE
      exact le_of_tendsto ht.norm (hev.mono fun n hn => hFb _ _ hn)
    · rw [indicator_of_notMem hωE, norm_zero]
      exact zero_le_one
  refine ae_condExp_eq_of_forall_setIntegral (mΩ := mΩ) (μ := P) (m := m)
    hm hE hX hG.stronglyMeasurable hGi ?_
  intro B hB
  exact setIntegral_eq_of_dyadic (mΩ := mΩ) (μ := P) hX hXb 𝓜 h𝓜 hFb hdet hτ
    ((hm _ hB).inter (hm _ hE)) (hread B hB)
    (hlim.mono fun ω hω hωBE => hω hωBE.2)

end InteractingSLE.Sec5.CrossCond.Gen
