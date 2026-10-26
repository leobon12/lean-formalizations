import SupercriticalConformalCovariance.TV.MarkovVersion

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set LQGMetric LQGMetric.GM QuantumZipper

namespace SupercriticalConformalCovariance.TV

/-- Uniform second moments for the continuous representative of the harmonic
part on a fixed inner disk. -/
theorem integral_sq_radialRepresentative_sub_zero_le
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hH hZ G : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (hGm : Measurable G) (hGeq : hH =ᵐ[P] G)
    (D : TopologicalSpace.Opens ℂ) (hDb : Bornology.IsBounded (D : Set ℂ))
    {L r δ S : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r < L)
    (hδ : 0 < δ) (hS : 0 ≤ S) (hSr : S + δ < r)
    (hBD : ball (0 : ℂ) L ⊆ D)
    (X : BddOn (D : Set ℂ) → Ω → ℝ)
    (hX : IsZBGFFProcessExt D X P)
    (hEq : ∀ φ : TestOn D, X φ.toBddOn =ᵐ[P]
      fun ω => restrictTo D (hZ ω) φ)
    (hind : IndepFun hH hZ P)
    {s : ℝ} (z : ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω)
    {y : ℂ} (hyS : ‖y‖ ≤ S) :
    ∫ ω, (radialRepresentative δ hδ (G ω) y -
      radialRepresentative δ hδ (G ω) 0) ^ 2 ∂P ≤
      diskVarianceEnvelope L S := by
  have hy : ‖y‖ + δ < r := by linarith
  have h0 : δ < r := by linarith
  have hSL : S < L := by linarith
  have hraw := integral_sq_markov_radDiff_div_le hh hGm hGeq D hDb
    hL hr hrL hδ hy h0 hBD X hX hEq hind z hsum
  have hmono := diskVarianceEnvelope_mono_radius hL hS hSL hyS
  simp_rw [radialRepresentative_sub_zero]
  exact hraw.trans hmono

end SupercriticalConformalCovariance.TV
