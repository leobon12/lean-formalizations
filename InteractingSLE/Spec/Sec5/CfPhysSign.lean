/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfPhysGlue

/-!
# Sign symmetry of projection-member identities

Packet PROVE-CFCHART2. The projection Gaussian factor is real. Conjugating its
identity proves the same assertion for the negative field, as required by the
counterflow image convention.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfPhys

open Coupling LocalSets Restart.DomainMarkov Restart.DomainMarkov.K2

/-- Projection-member identities are invariant under changing the sign of the
whole field. -/
theorem hasSafeMembers_neg {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {F : Set Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ}
    {X : Ω → DistOn upperHalfPlaneOpens} (h : HasSafeMembers P 𝓕 F ζ W X) :
    HasSafeMembers P 𝓕 F ζ W (fun ω => -X ω) := by
  intro s Fb hFb D hD hDs f Ξ
  have hc : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun ω => Complex.exp (Complex.I * ((-X ω) φ : ℂ))) =
        fun ω => starRingEnd ℂ (Complex.exp (Complex.I * (X ω φ : ℂ))) := by
    intro φ
    funext ω
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 1
    simp only [neg_apply, Complex.ofReal_neg]
    ring
  have key := congrArg (starRingEnd ℂ) (h s Fb hFb D hD hDs f Ξ)
  rw [map_mul, ← integral_conj, ← integral_conj] at key
  have hfac : starRingEnd ℂ (projFactor (ballsOpen Fb) f Ξ) = projFactor (ballsOpen Fb) f Ξ := by
    change starRingEnd ℂ (Complex.exp ((_ : ℝ) : ℂ)) = Complex.exp ((_ : ℝ) : ℂ)
    rw [← Complex.exp_conj, Complex.conj_ofReal]
  rw [hfac] at key
  change (∫ ω in D, Complex.exp (Complex.I * ((-X ω) (lapTest (ballsOpen Fb) f + Ξ) : ℂ)) ∂P) = _
  rw [hc, hc]
  exact key

/-- Negating a transported field reverses both deterministic shift coefficients. -/
theorem neg_chartTransport {c : Chart} (hc : c.IsConformal) (a k : ℝ)
    (h : DistOn upperHalfPlaneOpens) :
    -Chart.chartTransport hc 1 a k h = Chart.chartTransport hc 1 (-a) (-k) (-h) := by
  ext φ
  simp only [neg_apply, Chart.chartTransport_apply', one_mul]
  ring

end InteractingSLE.Sec5.CfPhys
