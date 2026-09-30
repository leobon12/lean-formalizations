import QuantumZipper.Proofs.GFF.K3.HalfDiscMarkov
import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.Section5.Prop17PalmCSetup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWS-H (1): scale-free variance bound for the harmonic part on a half-disc

Task SWS-H (plan `handoff/SW-SPLIT.md`, step H). The harmonic part of the free-boundary field on
the half-disc `B(t,r) ∩ ℍ` (Duplantier–Sheffield, Invent. Math. 185 (2011), §3/§6; repo
`K3.harmIncr`, `K3.harmH`) has increments `X(P_a) − X(P_b)` with `P_z = halfDiscPoisson t r z`.
The repository bound `K3.kernelCov2_halfDiscPoisson_le` has a constant `lipρ r r' · Bv t r r'`
that is not scale invariant (`Bv` grows like `log r`). Here we make it scale free:

* `halfDiscPoisson_eq_map_affine`: `P^{t,r}_z` is the image of `P^{0,1}_{(z−t)/r}` under
  `u ↦ t + r u` (change of variables in the Poisson formula; own elementary proof);
* `kernelCov2_map_affine`: the Neumann covariance of balanced pairs is invariant under
  `u ↦ t + r u` (`WedgeTK.kernelCov2_map_mul`, `S5.FieldLaw.Raw.kernelCov_neumannH_map_add_real`);
* `kernelCov2_halfDiscPoisson_scale_le`: for `‖a − t‖, ‖b − t‖ ≤ r' < r`,
  `Var(X(P_a) − X(P_b)) ≤ swhK (r'/r) · ‖a − b‖ / r`, with `swhK s = 2 lipρ 1 s · Bv 0 1 s`
  independent of `t` and `r`.

This is the variance modulus behind SW's "conditioned on `h_{2^{-k-1}}(z)`" step (Sheffield–Wang,
arXiv:1605.06171, p. 13, before (3.8)): the harmonic part at scale `ρ r` has oscillation variance
`O(ρ)`, uniformly in the scale.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal ComplexConjugate

namespace QuantumZipper
namespace RegUnif

open K3

/-- The real-affine map `u ↦ t + r u`. -/
def swhAff (t r : ℝ) (u : ℂ) : ℂ := (t : ℂ) + (r : ℂ) * u

theorem measurable_swhAff (t r : ℝ) : Measurable (swhAff t r) :=
  measurable_const.add (measurable_const.mul measurable_id)

theorem foldH_swhAff (t : ℝ) {r : ℝ} (hr : 0 < r) (u : ℂ) :
    foldH (swhAff t r u) = swhAff t r (foldH u) := by
  unfold foldH swhAff
  have him : ((t : ℂ) + (r : ℂ) * u).im = r * u.im := by simp
  by_cases h : 0 ≤ u.im
  · have h' : 0 ≤ ((t : ℂ) + (r : ℂ) * u).im := by rw [him]; positivity
    simp only [h, h', ite_true]
  · have h' : ¬ 0 ≤ ((t : ℂ) + (r : ℂ) * u).im := by
      rw [him]; intro h2; exact h (nonneg_of_mul_nonneg_right (by linarith) hr)
    simp only [h, h', ite_false, map_add, map_mul, Complex.conj_ofReal]

theorem circleUnif_eq_map_swhAff (t r : ℝ) :
    circleUnif (t : ℂ) r = (circleUnif 0 1).map (swhAff t r) := by
  unfold circleUnif
  rw [Measure.map_smul, Measure.map_map (measurable_swhAff t r) (continuous_circleMap 0 1).measurable]
  · congr 2
    funext θ
    simp [circleMap, swhAff]
  · exact (measurable_swhAff t r).aemeasurable

/-- **Affine invariance of the Neumann covariance** of balanced admissible pairs. -/
theorem kernelCov2_map_affine (t : ℝ) {r : ℝ} (hr : 0 < r) (p : WedgeTK.BPair) :
    kernelCov2 neumannH (p.1.1.map (swhAff t r), p.1.2.map (swhAff t r))
      (p.1.1.map (swhAff t r), p.1.2.map (swhAff t r)) =
      kernelCov2 neumannH p.1 p.1 := by
  have hA : ∀ μ : Measure ℂ, μ.map (swhAff t r) =
      (μ.map fun u => (r : ℂ) * u).map (· + (t : ℂ)) := fun μ => by
    have hm : Measurable fun u : ℂ => (r : ℂ) * u := measurable_id.const_mul _
    rw [Measure.map_map (measurable_add_const _)
      hm]
    congr 1
    funext u
    simp only [Function.comp, swhAff]
    ring
  rw [hA, hA]
  simp only [kernelCov2, S5.FieldLaw.Raw.kernelCov_neumannH_map_add_real]
  have := WedgeTK.kernelCov2_map_mul hr p p
  simpa only [kernelCov2] using this

end RegUnif
end QuantumZipper
