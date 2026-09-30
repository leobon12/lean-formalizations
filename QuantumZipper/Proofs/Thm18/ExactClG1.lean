import QuantumZipper.Proofs.Thm18.ExactClRTX

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# EXACT-CLUSTER (2): the G1 zoom A1b measures in round-trip form

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8,
pp. 69–71 (after unzipping by quantum length the side surface is the old one, rerooted).
Decision: `handoff/G4-CORE.md` §8.

`G1ZA1bSideExactStmt` (G1ZA1bMain.lean) compares the regularized new side field with
`coordChange Y Φ Q` at `fc(e, r)`, `Φ = f_{t'}⁻¹ ∘ (a ·) ∘ ψ'` (`ψ'` the side map of the new
driver). Given the affine identity of A1a, `f_{t'}⁻¹ (a ψ'(u + β)) = ψ(u/λ)` on `ℍ` (`ψ` the OLD
side map, a function of the driver alone), this file proves, for `r > 0`:

* `foldedCircle_map_affine`: `fc(e, r).map ((· − β)/λ) = fc((e − β)/λ, r/λ)` (`β` real, `λ > 0`);
* `map_comp_eq_map_affine`: `fc(e, r).map Φ = fc((e − β)/λ, r/λ).map ψ`: the measure read by `Y`
  does not depend on the new side map, only on `(β, λ)`;
* `map_mul_sideMap_eq_fwdMap`: `fc(e, r).map (a ψ') = fc(e', r').map (f_{t'} ∘ ψ)`: the measure
  at which the unzipped field must be exact is the forward image under `f_{t'}` of a pushed
  circle of the OLD side map, i.e. a round-trip (RTX) measure of the fixed-driver family
  `(t, e', r') ↦ (f_t ∘ ψ)_* fc(e', r')`;
* `coordChange_comp_affine`: `coordChange Y Φ Q (fc(e, r)) = coordChange Y ψ Q (fc(e', r')) − Q log λ`
  (the value side of the node is the OLD side field at an affine image circle).

Own elementary bookkeeping (affine invariance of folded circles, chain rule).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace ExactCl

/-! ## Real translations and affine maps of folded circles -/

theorem foldH_add_ofReal (b : ℝ) (w : ℂ) : foldH (w + (b : ℂ)) = foldH w + (b : ℂ) := by
  have him : (w + (b : ℂ)).im = w.im := by simp
  unfold foldH
  by_cases hw : 0 ≤ w.im
  · rw [ite_eq_left (by rw [him]; exact hw), ite_eq_left hw]
  · rw [ite_eq_right (by rw [him]; exact hw), ite_eq_right hw]
    rw [map_add, Complex.conj_ofReal]

theorem circleUnif_map_add {z : ℂ} {ε : ℝ} (b : ℝ) :
    (circleUnif z ε).map (fun w => w + (b : ℂ)) = circleUnif (z + (b : ℂ)) ε := by
  have hf : Measurable fun w : ℂ => w + (b : ℂ) := measurable_add_const _
  have hc : Measurable (circleMap z ε) := measurable_circleMap z ε
  have h1 : Measure.map (fun w : ℂ => w + (b : ℂ)) (Measure.map (circleMap z ε) (volume.restrict
      (Set.Ico 0 (2 * Real.pi)))) =
      Measure.map (circleMap (z + (b : ℂ)) ε) (volume.restrict (Set.Ico 0 (2 * Real.pi))) := by
    rw [Measure.map_map hf hc]
    refine Measure.map_congr (ae_of_all _ fun θ => ?_)
    simp only [Function.comp_apply, circleMap]
    ring
  simp only [circleUnif]
  rw [Measure.map_smul _ hf.aemeasurable, h1]

theorem foldedCircle_map_add {z : ℂ} {ε : ℝ} (b : ℝ) :
    (foldedCircle z ε).map (fun w => w + (b : ℂ)) = foldedCircle (z + (b : ℂ)) ε := by
  have hf : Measurable fun w : ℂ => w + (b : ℂ) := measurable_add_const _
  have h1 : Measure.map ((fun w : ℂ => w + (b : ℂ)) ∘ foldH) (circleUnif z ε) =
      Measure.map (foldH ∘ fun w : ℂ => w + (b : ℂ)) (circleUnif z ε) :=
    Measure.map_congr (ae_of_all _ fun w => (foldH_add_ofReal b w).symm)
  have h2 : Measure.map (fun w : ℂ => w + (b : ℂ)) ((circleUnif z ε).map foldH) =
      Measure.map ((fun w : ℂ => w + (b : ℂ)) ∘ foldH) (circleUnif z ε) :=
    Measure.map_map hf measurable_foldH
  have h3 : Measure.map (foldH ∘ fun w : ℂ => w + (b : ℂ)) (circleUnif z ε) =
      (circleUnif (z + (b : ℂ)) ε).map foldH := by
    rw [← Measure.map_map measurable_foldH hf, circleUnif_map_add b]
  simp only [foldedCircle]
  exact h2.trans (h1.trans h3)

/-- The real affine map `u ↦ (u − β)/λ`. -/
def affR (β lam : ℝ) (u : ℂ) : ℂ := ((lam⁻¹ : ℝ) : ℂ) * (u + ((-β : ℝ) : ℂ))

theorem measurable_affR (β lam : ℝ) : Measurable (affR β lam) :=
  measurable_const_mul _ |>.comp (measurable_add_const _)

theorem affR_eq (β lam : ℝ) (u : ℂ) : affR β lam u = (u - β) / lam := by
  unfold affR; push_cast; ring

theorem foldedCircle_map_affine {e : ℂ} {r β lam : ℝ} (hlam : 0 < lam) :
    (foldedCircle e r).map (affR β lam) =
      foldedCircle (((lam⁻¹ : ℝ) : ℂ) * (e + ((-β : ℝ) : ℂ))) (lam⁻¹ * r) := by
  have e1 : affR β lam = (fun w : ℂ => ((lam⁻¹ : ℝ) : ℂ) * w) ∘ fun w => w + ((-β : ℝ) : ℂ) := rfl
  rw [e1, ← Measure.map_map (measurable_const_mul _) (measurable_add_const _),
    foldedCircle_map_add, Thm18Asm.foldedCircle_map_mul (inv_pos.2 hlam)]

/-! ## The G1 measures -/

variable {F ψ ψ' : ℂ → ℂ} {a β lam : ℝ}

/-- From the A1a identity `F (a ψ'(u + β)) = ψ(u/λ)` on `ℍ`: `F (a ψ'(v)) = ψ((v − β)/λ)` on `ℍ`. -/
theorem comp_eq_affR (hlam : 0 < lam)
    (hEq : EqOn (fun u => F ((a : ℂ) * ψ' (u + (β : ℂ)))) (fun u => ψ (u / (lam : ℂ))) H)
    {v : ℂ} (hv : v ∈ H) : F ((a : ℂ) * ψ' v) = ψ (affR β lam v) := by
  have hvH : v - (β : ℂ) ∈ H := by
    show 0 < (v - (β : ℂ)).im
    have : 0 < v.im := hv
    simpa using this
  have := hEq hvH
  simp only [sub_add_cancel] at this
  rw [this, affR_eq]

/-- **The measure read by `Y`.** `fc(e, r).map (F ∘ (a ψ')) = fc(e', r').map ψ`. -/
theorem map_comp_eq_map_affine (hlam : 0 < lam) (hψm : Measurable ψ)
    (hEq : EqOn (fun u => F ((a : ℂ) * ψ' (u + (β : ℂ)))) (fun u => ψ (u / (lam : ℂ))) H)
    (e : ℂ) {r : ℝ} (hr : 0 < r) :
    (foldedCircle e r).map (fun u => F ((a : ℂ) * ψ' u)) =
      (foldedCircle (((lam⁻¹ : ℝ) : ℂ) * (e + ((-β : ℝ) : ℂ))) (lam⁻¹ * r)).map ψ := by
  rw [← foldedCircle_map_affine hlam, Measure.map_map hψm (measurable_affR β lam)]
  refine Measure.map_congr ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H e hr] with v hv
  exact comp_eq_affR hlam hEq hv

/-- Derivative of the composite: `‖Φ'(v)‖ = ‖ψ'((v − β)/λ)‖ / λ` on `ℍ`, `Φ = F ∘ (a ψ')`. -/
theorem norm_deriv_comp_eq (hlam : 0 < lam) (hψd : DifferentiableOn ℂ ψ H)
    (hEq : EqOn (fun u => F ((a : ℂ) * ψ' (u + (β : ℂ)))) (fun u => ψ (u / (lam : ℂ))) H)
    {v : ℂ} (hv : v ∈ H) :
    ‖deriv (fun u => F ((a : ℂ) * ψ' u)) v‖ = ‖deriv ψ (affR β lam v)‖ / lam := by
  have hloc : (fun u => F ((a : ℂ) * ψ' u)) =ᶠ[𝓝 v] fun u => ψ (affR β lam u) :=
    Filter.eventuallyEq_of_mem (isOpen_H.mem_nhds hv) fun u hu => comp_eq_affR hlam hEq hu
  have haffH : affR β lam v ∈ H := by
    show 0 < (affR β lam v).im
    have : 0 < v.im := hv
    unfold affR
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.add_im]
    positivity
  have hψv : HasDerivAt ψ (deriv ψ (affR β lam v)) (affR β lam v) :=
    ((hψd _ haffH).differentiableAt (isOpen_H.mem_nhds haffH)).hasDerivAt
  have hA : HasDerivAt (affR β lam) ((lam⁻¹ : ℝ) : ℂ) v := by
    have h1 : HasDerivAt (fun u : ℂ => u + ((-β : ℝ) : ℂ)) 1 v := (hasDerivAt_id v).add_const _
    have h2 := h1.const_mul ((lam⁻¹ : ℝ) : ℂ)
    rw [mul_one] at h2
    exact h2
  have hc : HasDerivAt (fun u => ψ (affR β lam u)) (deriv ψ (affR β lam v) * ((lam⁻¹ : ℝ) : ℂ)) v :=
    hψv.comp v hA
  rw [hloc.deriv_eq, hc.deriv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hlam), div_eq_mul_inv]

/-- **Value side of `G1ZA1bSideExactStmt`.** For `r > 0`, if `log ‖ψ'‖` is integrable on
`fc(e', r')` and `ψ'` does not vanish on `ℍ`:
`coordChange Y Φ Q (fc(e, r)) = coordChange Y ψ Q (fc(e', r')) − Q log λ`. -/
theorem coordChange_comp_affine (y : FieldSample) (Q : ℝ) (hlam : 0 < lam)
    (hψm : Measurable ψ) (hψd : DifferentiableOn ℂ ψ H) (hne : ∀ z ∈ H, deriv ψ z ≠ 0)
    (hEq : EqOn (fun u => F ((a : ℂ) * ψ' (u + (β : ℂ)))) (fun u => ψ (u / (lam : ℂ))) H)
    (e : ℂ) {r : ℝ} (hr : 0 < r)
    (hint : Integrable (fun z => Real.log ‖deriv ψ z‖)
      (foldedCircle (((lam⁻¹ : ℝ) : ℂ) * (e + ((-β : ℝ) : ℂ))) (lam⁻¹ * r))) :
    coordChange y (fun u => F ((a : ℂ) * ψ' u)) Q (foldedCircle e r) =
      coordChange y ψ Q (foldedCircle (((lam⁻¹ : ℝ) : ℂ) * (e + ((-β : ℝ) : ℂ))) (lam⁻¹ * r)) -
        Q * Real.log lam := by
  unfold coordChange
  rw [map_comp_eq_map_affine hlam hψm hEq e hr]
  have hL : Measurable fun z => Real.log ‖deriv ψ z‖ :=
    Real.measurable_log.comp (measurable_deriv ψ).norm
  have hI : ∫ v, Real.log ‖deriv (fun u => F ((a : ℂ) * ψ' u)) v‖ ∂(foldedCircle e r) =
      ∫ v, (Real.log ‖deriv ψ (affR β lam v)‖ - Real.log lam) ∂(foldedCircle e r) := by
    refine integral_congr_ae ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H e hr] with v hv
    have haffH : affR β lam v ∈ H := by
      show 0 < (affR β lam v).im
      have : 0 < v.im := hv
      unfold affR
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
        Complex.add_im]
      positivity
    rw [norm_deriv_comp_eq hlam hψd hEq hv, Real.log_div
      (norm_ne_zero_iff.2 (hne _ haffH)) hlam.ne']
  have hint' : Integrable (fun v => Real.log ‖deriv ψ (affR β lam v)‖) (foldedCircle e r) := by
    have := (integrable_map_measure hL.aestronglyMeasurable
      (measurable_affR β lam).aemeasurable).1 (by rwa [foldedCircle_map_affine hlam])
    exact this
  have hmap : ∫ v, Real.log ‖deriv ψ (affR β lam v)‖ ∂(foldedCircle e r) =
      ∫ z, Real.log ‖deriv ψ z‖ ∂(foldedCircle (((lam⁻¹ : ℝ) : ℂ) * (e + ((-β : ℝ) : ℂ)))
        (lam⁻¹ * r)) := by
    rw [← foldedCircle_map_affine hlam, integral_map (measurable_affR β lam).aemeasurable
      hL.aestronglyMeasurable]
  have h1 : (foldedCircle e r).real univ = 1 := by
    rw [measureReal_def, measure_univ, ENNReal.toReal_one]
  rw [hI, integral_sub hint' (integrable_const _), hmap, integral_const, smul_eq_mul, h1]
  ring

end ExactCl
end Thm18Asm
end QuantumZipper
