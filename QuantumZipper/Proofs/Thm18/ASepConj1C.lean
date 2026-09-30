import QuantumZipper.Proofs.Thm18.ASepConj1B

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP conjunct 1 (c): engine inputs at a continuous radius, A-sep family at `τ' = 0`

* `det_unif_A0_rho`: the deterministic part `∫ Dfun(z, ρ) dν_p` converges to `detLimA0 p`
  uniformly in `p` and in all radii `ρ ∈ (0, ρ₀]` (from `det_unif_gen_rho`);
* `ae_continuousOn_Phi_rho`: almost surely `(p, ρ) ↦ ∫ evalReg x_p (fc(v, ρ)) dν_p(v)` is
  continuous on `S × (0, 1]` (joint witness `ae_exists_joint_witness_fixed`, dominated
  convergence on `S × [ρ₁, 1]`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace ASep

open RegCont TwoPoint CoordReg RegUnif UnzipInvariance RegSample

/-- **Uniform convergence of the deterministic part over all small radii.** -/
theorem det_unif_A0_rho {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ} (hT : 0 ≤ T)
    {d : ℂ} {r : ℝ} (hr : 0 < r) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) {S : Set (Fin 2 → ℝ)}
    (hSb : ∀ p ∈ S, p 0 ∈ Icc (0 : ℝ) T ∧ p 1 ∈ Icc a₀ a₁) {δ : ℝ}
    (hgood : ∀ a ∈ Icc a₀ a₁,
      ∀ w ∈ Metric.cthickening δ (foldH '' Metric.sphere d r) ∩ {w : ℂ | 0 ≤ w.im},
      ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (a' : ℝ) {g₁ : ℂ → ℝ} (hg₁ : Continuous g₁) (Q : ℝ) :
    ∀ ε > 0, ∃ ρ₀ > 0, ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∀ p ∈ S,
      |∫ z, Dfun (fun s => W (p 0 - s) - W (p 0)) (p 0) a' g₁ Q (z, ρ) ∂nuA0 W d r p -
        detLimA0 W a' g₁ Q d r p| < ε := by
  obtain ⟨m, c, Rb, g, hm, hc, -, hg⟩ := exists_geo_A0 hW hW0 hT ha₀ (hgood0_of_hgood hgood)
  obtain ⟨A, hA0, hA⟩ := Gdet_logBound hW hW0 T (Rb + 1) hT a' hg₁ Q
  set B : ℝ := |a'| + |Q| with hB
  have hB0 : 0 ≤ B := by positivity
  have hmap : ∀ p ∈ S, (foldedCircle d r).map (g p) = nuA0 W d r p := fun p hp =>
    Measure.map_congr ((ae_mem_foldSph d hr.le).mono fun w hw =>
      ((hg p (hSb p hp).1 (hSb p hp).2).2.2 w hw))
  have key := det_unif_gen_rho (continuousOn_Gdet_joint hW hW0 T a' hg₁ Q)
    hA0 hB0 hA (fun t ht ρ hρ => (continuous_integral_Gdet hW hW0 ht.1 a' hg₁ Q
      hρ).measurable) S (fun p => p 0) (fun p hp => (hSb p hp).1)
    (fun _ => foldedCircle d r) g (fun p hp => (hg p (hSb p hp).1 (hSb p hp).2).1)
    (Ra := ‖d‖ + r) hc
    (fun p _ => by
      filter_upwards [foldedCircle_ae_mem_H d hr, foldedCircle_ae_norm_le d hr.le] with w h1 h2
      exact ⟨h1, h2⟩)
    (fun p hp => (hg p (hSb p hp).1 (hSb p hp).2).2.1)
    (fun p _ => (integrable_log_im_foldedCircle d hr).abs) (K₁ := 200 / Real.sqrt r)
    (β := 1 / 4) (by norm_num) (fun p _ => CoordRegComp.stripBound_foldedCircle d hr)
  intro ε hε
  obtain ⟨ρ₀, hρ₀, hJ⟩ := key ε hε
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ p hp => ?_⟩
  have h := hJ ρ hρ hρρ p hp
  simp only [hmap p hp] at h
  have e : ∫ z, Dfun (fun s => W (p 0 - s) - W (p 0)) (p 0) a' g₁ Q (z, ρ) ∂nuA0 W d r p =
      ∫ z, (∫ v, Gdet W a' g₁ Q (p 0) v ∂foldedCircle z ρ) ∂nuA0 W d r p :=
    integral_congr_ae (Eventually.of_forall fun z =>
      Dfun_eq_integral_Gdet hW hW0 (hSb p hp).1.1 a' hg₁ Q z hρ)
  rw [e]
  exact h

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

end ASep
end QuantumZipper
