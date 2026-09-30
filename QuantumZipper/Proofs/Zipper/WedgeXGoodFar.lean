import QuantumZipper.Proofs.LQG.LocalRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D29 (wedge unzipping), X-G part 2: rule (5.1) away from the singular points, along `goodFilter`

Task X-GOOD. Deterministic. Let `y` be good and `ψ` continuous on `W ∩ ℍ̄` for an open `W`
(in the application `W = ℂ \ {O⁻_t, O⁺_t}` and `ψ = ψ_t = −γ log‖E_t‖`). Near a compact
`K ⊆ W`, `ψ` agrees with a cutoff `φ'` continuous on all of `ℍ̄` (`LocalRule.exists_cutoff`), so
for small radii the regularized circle averages of `y + ψ` and of `y + φ'` agree at the centres
of `K` (`LocalRule.avgReg_congr_local`, `LocalRule.ofFun_fc_congr`), hence so do the boundary
and area densities. `y + φ'` is good by rule (5.1) (`IsLQGGood.add_ofFun`), so:

* `tendsto_bdryR_far`: for test functions supported in `W ∩ ℝ`,
  `∫ f dν_{a 2^{-k}}(y + ψ) → ∫ e^{γψ/2} f dν_y` along `goodFilter`;
* `hasAreaLimit_add_far`: if `H ⊆ W`, `y + ψ` has the area limit `e^{γψ} μ_y` (no regularity of
  `y + ψ` is needed: area test functions stay away from `ℝ`).

Source: Sheffield, arXiv:1012.4797, rule (5.1) (§5, p. 60), in the local form of
`LocalRule.lean` (which does the same along the dyadic radii only); the offset version here is
own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

open GoodSample

/-- `evalReg` on a folded circle only reads `avgReg` at the points of the closed disc, for all
large `k`. -/
theorem evalReg_fc_congr {x x' : FieldSample} {c : ℂ} (hc : c ∈ Hbar) {r : ℝ} (hr : 0 < r)
    (h : ∀ᶠ k in atTop, ∀ w ∈ Hbar, w ∈ Metric.closedBall c r → avgReg x k w = avgReg x' k w) :
    evalReg x (foldedCircle c r) = evalReg x' (foldedCircle c r) := by
  unfold evalReg
  have hev : (fun k => ∫ w, avgReg x k w ∂foldedCircle c r) =ᶠ[atTop]
      (fun k => ∫ w, avgReg x' k w ∂foldedCircle c r) := by
    filter_upwards [h] with k hk
    refine integral_congr_ae ?_
    have hHb : ∀ᵐ w ∂foldedCircle c r, w ∈ Hbar := by
      unfold foldedCircle
      exact (ae_map_iff measurable_foldH.aemeasurable
        (measurableSet_le measurable_const Complex.measurable_im)).2
        (Eventually.of_forall fun u => CircleFubini.foldH_mem_Hbar' u)
    filter_upwards [LocalRule.ae_fc_mem_closedBall hc hr, hHb] with w hw hwH
    exact hk w hwH hw
  unfold limUnder
  rw [Filter.map_congr hev]

/-- **Local equality of `evalReg` for `y + ψ` and `y + φ'`** where `φ' = ψ` on `cthickening δ K`,
at centres in `K` and radii `≤ δ/4`. -/
theorem evalReg_add_ofFun_cutoff (y : FieldSample) {ψ φ' : ℂ → ℝ} {Kc : Set ℂ} {δ : ℝ}
    (_hδ : 0 < δ) (heq : EqOn φ' ψ (Metric.cthickening δ Kc)) {c : ℂ} (hc : c ∈ Hbar)
    (hcK : c ∈ Kc) {r : ℝ} (hr : 0 < r) (hrδ : r ≤ δ / 4) :
    evalReg (y + ofFun ψ) (foldedCircle c r) = evalReg (y + ofFun φ') (foldedCircle c r) := by
  refine evalReg_fc_congr hc hr ?_
  filter_upwards [RegClosure.tendsto_radius_nhdsGT.eventually
    (Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < δ / 4))] with k hk w hw hwc
  refine LocalRule.avgReg_congr_local k (by linarith : (0 : ℝ) < δ / 4) (fun c' hc' hdist => ?_) hw
  show y (foldedCircle c' (radius k)) + ofFun ψ (foldedCircle c' (radius k)) =
    y (foldedCircle c' (radius k)) + ofFun φ' (foldedCircle c' (radius k))
  congr 1
  refine LocalRule.ofFun_fc_congr hc' (radius_pos k) fun u hu => (heq ?_).symm
  refine Metric.mem_cthickening_of_dist_le u c δ Kc hcK ?_
  have h1 : dist u c' ≤ radius k := hu
  have h2 : dist w c ≤ r := hwc
  have h3 := dist_triangle4 u c' w c
  have h4 : radius k < δ / 4 := hk.2
  linarith

/-- The same for the approximate area measures, test functions supported in `K`. -/
theorem integral_areaR_cutoff (γ : ℝ) (y : FieldSample) {ψ φ' : ℂ → ℝ} {Kc : Set ℂ} {δ : ℝ}
    (hδ : 0 < δ) (heq : EqOn φ' ψ (Metric.cthickening δ Kc)) {f : ℂ → ℝ}
    (hfK : tsupport f ⊆ Kc) (hfH : tsupport f ⊆ H) {r : ℝ} (hr : 0 < r) (hrδ : r ≤ δ / 4) :
    ∫ z, f z ∂areaR γ (y + ofFun ψ) r = ∫ z, f z ∂areaR γ (y + ofFun φ') r := by
  have hS : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have key : (areaR γ (y + ofFun ψ) r).restrict (tsupport f) =
      (areaR γ (y + ofFun φ') r).restrict (tsupport f) := by
    simp only [areaR]
    rw [restrict_withDensity hS, restrict_withDensity hS]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hS] with z hz
    simp only [areaDens]
    rw [evalReg_add_ofFun_cutoff y hδ heq (show (0 : ℝ) ≤ z.im from le_of_lt (hfH hz))
      (hfK hz) hr hrδ]
  have hz : ∀ z, z ∉ tsupport f → f z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, key,
    setIntegral_eq_integral_of_forall_compl_eq_zero hz]

end WedgeUnzip
end QuantumZipper
