import QuantumZipper.Proofs.LQG.CoordChangeMain
import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.LQG.GoodMeasurableReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z3-ADDFUN: the fixed-map coordinate-change rule survives adding a continuous function

Deterministic, per sample (decision D58). Let `x` be a regular sample, `ψ` holomorphic near
`J = [a, b]`, real on `J` with `ψ = Φ` there (`Φ : ℝ ≃o ℝ`), `ψ' ≠ 0` on `J`, and `φ` continuous
on `V ∩ Hbar` for an open `V ⊇ Φ(J)`. If `bdryApprox γ (coordChange x ψ Q)` converges vaguely on
`(a, b)` to `ψ⁻¹_*(ν|_{Φ(J°)})`, then `bdryApprox γ (coordChange (x + φ) ψ Q)` converges vaguely
on `(a, b)` to `ψ⁻¹_*((e^{γφ/2} ν)|_{Φ(J°)})` (`isVagueLimitOnR_coordChange_add_ofFun`).

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
rule (5.1) / Prop. 2.1 (`h ↦ h + φ` multiplies the boundary measure by `e^{γφ/2}`), combined with
the coordinate change rule (Sheffield, arXiv:1012.4797, (1.3)). The proof follows the repository's
`LocalRule.isVagueLimitOnR_add_ofFun` (density part) and `WedgeUnzip.unzipAddFun` (the field
identity `evalReg (x + φ) ν = evalReg x ν + ∫ φ dν` on pushed semicircles).

Steps: (1) on the compact image `Kψ ⊆ Hbar ∩ V` of the small half-discs,
`avgReg (x + φ) j = avgReg x j + (circle average of φ')` with `φ'` a cutoff of `φ`;
(2) hence `evalReg (x + φ) (pc ψ s r) = evalReg x (pc ψ s r) + ∫ φ' d(pc ψ s r)`;
(3) `∫ φ' d(pc ψ s r) = smoothFun G s r` for a cutoff `G` of `φ' ∘ ψ`, continuous in `s`,
so the dyadic limits add; (4) the exponential weights `e^{γ/2 smoothFun G t r_k}` converge
uniformly on compacts (`GoodSample.tendsto_integral_exp_mul`), and the limit weight is
`e^{γ/2 φ(Φ t)}`, which is transported through `targetMeasure`.
-/

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z3

open GoodSample LocalRule CoordChange GaussTK

theorem integrable_of_ae_mem_z3 {μ : Measure ℂ} [IsFiniteMeasure μ] {K : Set ℂ}
    (hK : IsCompact K) (hKH : K ⊆ Hbar) (hμ : ∀ᵐ w ∂μ, w ∈ K) {g : ℂ → ℝ}
    (hg : ContinuousOn g Hbar) : Integrable g μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem hμ]
  exact (hg.mono hKH).integrableOn_compact hK

/-- **Field identity on measures carried by `Kψ`** (cf. `WedgeUnzip.unzipAddFun`). -/
theorem evalReg_add_ofFun_of_ae_z3 {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    {φ φ' : ℂ → ℝ} (hφ' : ContinuousOn φ' Hbar) {Kψ : Set ℂ} (hK : IsCompact Kψ)
    (hKH : Kψ ⊆ Hbar) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (heq : EqOn φ' φ (cthickening δ₀ Kψ))
    {ν : Measure ℂ} [IsProbabilityMeasure ν] (hν : ∀ᵐ w ∂ν, w ∈ Kψ) {L : ℝ}
    (hL : Tendsto (fun j => ∫ w, avgReg x j w ∂ν) atTop (𝓝 L)) :
    evalReg (x + ofFun φ) ν = evalReg x ν + ∫ w, φ' w ∂ν := by
  have hF' := gs_add_ofFun hF hφ'
  have hrad : ∀ᶠ j in atTop, radius j < δ₀ / 2 :=
    (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (gt_mem_nhds (by linarith))
  have havg : ∀ j, radius j < δ₀ / 2 → ∀ w ∈ Kψ,
      avgReg (x + ofFun φ) j w = avgReg x j w + smoothFun φ' w (radius j) := by
    intro j hj w hw
    have e1 : avgReg (x + ofFun φ) j w = avgReg (x + ofFun φ') j w := by
      refine avgReg_congr_local j (by linarith : 0 < δ₀ / 2) (fun c hc hcw => ?_) (hKH hw)
      simp only [Pi.add_apply]
      rw [ofFun_fc_congr hc (radius_pos j) (fun u hu => ?_)]
      have hut : dist u w ≤ δ₀ := by
        have := dist_triangle u c w
        have := mem_closedBall.1 hu
        linarith
      exact (heq (mem_cthickening_of_dist_le u _ δ₀ Kψ hw hut)).symm
    rw [e1, hF'.avgReg_eq j (hKH hw), hF.avgReg_eq j (hKH hw)]
    rfl
  have hint1 : ∀ j, Integrable (fun w => avgReg x j w) ν := fun j =>
    (integrable_of_ae_mem_z3 hK hKH hν (RegClosure.continuousOn_slice hF.1 (radius_pos j))).congr
      (hν.mono fun w hw => (hF.avgReg_eq j (hKH hw)).symm)
  have hint2 : ∀ j, Integrable (fun w => smoothFun φ' w (radius j)) ν := fun j =>
    integrable_of_ae_mem_z3 hK hKH hν (continuous_smoothFun hφ' _).continuousOn
  have hint3 : Integrable φ' ν := integrable_of_ae_mem_z3 hK hKH hν hφ'
  have hsm : Tendsto (fun j => ∫ w, smoothFun φ' w (radius j) ∂ν) atTop
      (𝓝 (∫ w, φ' w ∂ν)) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    filter_upwards [RegClosure.tendsto_radius_nhdsGT.eventually
      (smooth_unif hφ' hK hKH (ε / 2) (by positivity))] with j hj
    rw [Real.dist_eq, ← integral_sub (hint2 j) hint3]
    have := norm_integral_le_of_norm_le_const (μ := ν) (C := ε / 2)
      (f := fun w => smoothFun φ' w (radius j) - φ' w)
      (hν.mono fun w hw => by rw [Real.norm_eq_abs]; exact (hj w hw).le)
    simp only [probReal_univ, mul_one, Real.norm_eq_abs] at this
    linarith
  have hsum : Tendsto (fun j => ∫ w, avgReg (x + ofFun φ) j w ∂ν) atTop
      (𝓝 (L + ∫ w, φ' w ∂ν)) := by
    refine (hL.add hsm).congr' ?_
    filter_upwards [hrad] with j hj
    rw [← integral_add (hint1 j) (hint2 j)]
    exact integral_congr_ae (hν.mono fun w hw => (havg j hj w hw).symm)
  unfold evalReg
  rw [hsum.limUnder_eq, hL.limUnder_eq]

end G1Z3
end Thm18Asm
end QuantumZipper
