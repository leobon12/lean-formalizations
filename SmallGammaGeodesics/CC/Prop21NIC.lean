import SmallGammaGeodesics.CC.Prop21Pull
import SmallGammaGeodesics.CC.Prop21Tight

/-!
# [3] Prop 2.1: the fresh field on the NIC space and its identities (packet CC6b; CC0 D10)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D10**: on the NIC space
of the zoom at `(z, r)` (CC4 `zoom_nic`, CC6a `lemma23_zoom_exists`), with NIC data `(h, h̄, K)` of
`Ξinv` on `B_R` (`h ∘ χ = h̄ + K` there), `c = ϕ'(z)`, take
* the fresh domain field `x = h(c ·) − h_{|c|}(0)` (`zoomDom`, a normalized whole-plane GFF:
  `isWholePlaneGFF_rotDist`, `ae_circleAvg_rotDist`, `ae_circleAvg_affineComp`);
* the conformal-side field `h̄ − h_{|c|}(0)` and `f = K̃ + J + Q log|c⁻¹|`, where
  `J = (Q/2) log det DΞ` (`exists_zoomJac`) equals `Q log|χ'|` on `B_R`.

`nic_zoom_fields` proves:
1. `(x, h̄ − h_{|c|}(0), f)` is a.s. a conformal coupling of `(ϕ̃, W̃, ψ̃(B_{R/2}))`
   (`isConfCoupling_of_nic` and `IsConfCoupling.addConst`);
2. a.s. `D_x(u, v) = κ D_h(c u, c v)` with `κ = e^{−ξ(h_{|c|}(0) + Q log|c|)}` (complex affine
   covariance `IsCanonicalLQGMetric.ae_coord` and Weyl scaling by constants);
3. a.s. `D_x(u, v; c⁻¹ B_{R/2}) = κ D_h(c u, c v; B_{R/2})` (`internal_affineC_preimage_eq`);
4. a.s. `D^{ϕ̃}(u, v) = κ D_{h̄ + K̃ + J}(ϕ̃ u, ϕ̃ v; B_{R/2})` (Weyl scaling by constants of CC2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-! ## The Jacobian term -/

/-- `y ↦ det Df(y)` is continuous for `f` of class `C¹`. -/
theorem continuous_det_fderiv {f : ℂ → ℂ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    Continuous fun y => (fderiv ℝ f y).det := by
  have hc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have e : (fun y => (fderiv ℝ f y).det) = fun y =>
      ((fderiv ℝ f y) 1).re * ((fderiv ℝ f y) Complex.I).im -
        ((fderiv ℝ f y) 1).im * ((fderiv ℝ f y) Complex.I).re :=
    funext fun y => NIC.det_eq _
  rw [e]
  have h1 : Continuous fun y => (fderiv ℝ f y) 1 :=
    (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp hc
  have hI : Continuous fun y => (fderiv ℝ f y) Complex.I :=
    (ContinuousLinearMap.apply ℝ ℂ Complex.I).continuous.comp hc
  exact ((Complex.continuous_re.comp h1).mul (Complex.continuous_im.comp hI)).sub
    ((Complex.continuous_im.comp h1).mul (Complex.continuous_re.comp hI))

/-- **The Jacobian term** `J = (Q/2) log det DΞ`: continuous, `= Q log|Ξ'|` on `B_R`, and
`|J| ≤ 2 |Q| C r` everywhere. -/
theorem exists_zoomJac (γ : ℝ) {ϕ ψ : ℂ → ℂ} {W : Set ℂ} {z : ℂ} {r R C : ℝ}
    {Ξinv : ℂ → ℂ} (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv) (hCr0 : 0 ≤ C * r)
    (hCr : C * r ≤ 1 / 4) :
    ∃ jl : C(ℂ, ℝ), (∀ y ∈ ball (0 : ℂ) R,
        jl y = Q γ * Real.log ‖deriv (zoomExt ϕ ψ z r R) y‖) ∧
      ∀ y, |jl y| ≤ 2 * |Q γ| * (C * r) := by
  set Ξ := zoomExt ϕ ψ z r R with hΞ
  have hdet := det_fderiv_zoomExt_bounds hZ (by linarith)
  have hpos : ∀ y, 0 < (fderiv ℝ Ξ y).det := fun y => by linarith [(hdet y).1]
  have hcont : Continuous fun y => Q γ / 2 * Real.log (fderiv ℝ Ξ y).det :=
    continuous_const.mul ((continuous_det_fderiv hZ.nearId.contDiff_inv).log fun y =>
      (hpos y).ne')
  refine ⟨⟨fun y => Q γ / 2 * Real.log (fderiv ℝ Ξ y).det, hcont⟩, fun y hy => ?_, fun y => ?_⟩
  · show Q γ / 2 * Real.log (fderiv ℝ Ξ y).det = Q γ * Real.log ‖deriv Ξ y‖
    have h1 := abs_det_fderiv_zoomExt hZ hy
    rw [abs_of_pos (hpos y)] at h1
    rw [h1, Real.log_pow]
    push_cast
    ring
  · show |Q γ / 2 * Real.log (fderiv ℝ Ξ y).det| ≤ 2 * |Q γ| * (C * r)
    rw [abs_mul, abs_div, abs_two]
    have := abs_log_le_four_mul hCr0 hCr (hdet y).1 (hdet y).2
    have hQ := abs_nonneg (Q γ)
    calc |Q γ| / 2 * |Real.log (fderiv ℝ Ξ y).det| ≤ |Q γ| / 2 * (4 * (C * r)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * |Q γ| * (C * r) := by ring

/-! ## The fresh field and its identities -/

/-- The normalized fresh field `x(c ·) − x_{|c|}(0)`. -/
def zoomNorm (c : ℂ) (x : DistC) : DistC :=
  addConst (zoomDom c x) (-circleAvg x ‖c‖ 0)

variable {γ : ℝ} {D : DistC → ContMetric}

/-- `x(c ·)` is a whole-plane GFF. -/
theorem isWholePlaneGFF_zoomDom {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {c : ℂ} (hc : c ≠ 0) :
    IsWholePlaneGFF (fun ω => zoomDom c (h ω)) P :=
  GaussianLQG.isWholePlaneGFF_rotDist (hh.affineComp (norm_pos_iff.2 hc) 0)
    (GaussianLQG.norm_div_norm_eq_one hc)

/-- **The fresh field is a normalized whole-plane GFF** (`(x(c ·))_1(0) = x_{|c|}(0)` a.s.). -/
theorem isNormalizedWPGFF_zoomNorm {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {c : ℂ} (hc : c ≠ 0) :
    IsNormalizedWPGFF (fun ω => zoomNorm c (h ω)) P := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hg := isWholePlaneGFF_zoomDom hh hc
  have hcm : Measurable fun ω => -circleAvg (h ω) ‖c‖ 0 :=
    ((measurable_circleAvg_left ‖c‖ 0).comp hh.measurable).neg
  refine ⟨hg.addConst hcm, ?_⟩
  filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hg,
    GaussianLQG.ae_circleAvg_rotDist (hh.affineComp hcpos 0) (GaussianLQG.norm_div_norm_eq_one hc),
    CircleAvg.ae_circleAvg_affineComp hh hcpos 0] with ω h1 h2 h3
  show circleAvg (addConst (zoomDom c (h ω)) (-circleAvg (h ω) ‖c‖ 0)) 1 0 = 0
  rw [h1, zoomDom, h2, h3]
  ring

/-- **The fields on the NIC space of the zoom at `(z, r)` and their identities** (D10). -/
theorem nic_zoom_fields (hγ : 0 < γ) (hD : GaussianLQG.IsCanonicalLQGMetric γ D)
    {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ x ∈ W, ψ (ϕ x) = x)
    {z : ℂ} {r R C : ℝ} (hr : 0 < r) (hR : 0 < R) {Ξinv : ℂ → ℂ}
    (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv) (hCr : C * r ≤ 1 / 4)
    (hVt : zoomPsi ϕ ψ z r '' ball 0 (R / 2) ⊆ zoomSet z r V)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ}
    {h hbar : Ω → DistC} {K : Ω → ℂ → ℝ} (hc : IsNICCoupling P Ξinv (ball 0 R) B h hbar K)
    {Kt : Ω → C(ℂ, ℝ)} (hKtm : Measurable Kt)
    (hKt : ∀ ω, ∀ x ∈ ball (0 : ℂ) (R / 2), Kt ω x = K ω x) {jl : C(ℂ, ℝ)}
    (hjl : ∀ y ∈ ball (0 : ℂ) R, jl y = Q γ * Real.log ‖deriv (zoomExt ϕ ψ z r R) y‖) :
    IsNormalizedWPGFF (fun ω => zoomNorm (deriv ϕ z) (h ω)) P ∧
    IsWholePlaneGFF (fun ω => addConst (hbar ω) (-circleAvg (h ω) ‖deriv ϕ z‖ 0)) P ∧
    Measurable (fun ω => (Kt ω + jl) + ContinuousMap.const ℂ (Q γ * Real.log ‖(deriv ϕ z)⁻¹‖)) ∧
    (∀ᵐ ω ∂P, IsConfCoupling γ (zoomMap ϕ z r) (zoomSet z r W)
      (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) (zoomNorm (deriv ϕ z) (h ω))
      (addConst (hbar ω) (-circleAvg (h ω) ‖deriv ϕ z‖ 0))
      ((Kt ω + jl) + ContinuousMap.const ℂ (Q γ * Real.log ‖(deriv ϕ z)⁻¹‖))) ∧
    (∀ᵐ ω ∂P, ∀ u v : ℂ, (D (zoomNorm (deriv ϕ z) (h ω))).1 (u, v) =
      Real.exp (-(xiGamma γ * (circleAvg (h ω) ‖deriv ϕ z‖ 0 + Q γ * Real.log ‖deriv ϕ z‖))) *
        (D (h ω)).1 (deriv ϕ z * u, deriv ϕ z * v)) ∧
    (∀ᵐ ω ∂P, ∀ u v : ℂ, (D (zoomNorm (deriv ϕ z) (h ω))).internal
        ((fun w => deriv ϕ z * w) ⁻¹' ball 0 (R / 2)) u v =
      ENNReal.ofReal (Real.exp (-(xiGamma γ *
        (circleAvg (h ω) ‖deriv ϕ z‖ 0 + Q γ * Real.log ‖deriv ϕ z‖)))) *
        (D (h ω)).internal (ball 0 (R / 2)) (deriv ϕ z * u) (deriv ϕ z * v)) ∧
    (∀ᵐ ω ∂P, ∀ u v : ℂ, confMetric D (zoomMap ϕ z r) (zoomPsi ϕ ψ z r '' ball 0 (R / 2))
        (addConst (hbar ω) (-circleAvg (h ω) ‖deriv ϕ z‖ 0))
        ((Kt ω + jl) + ContinuousMap.const ℂ (Q γ * Real.log ‖(deriv ϕ z)⁻¹‖)) u v =
      ENNReal.ofReal (Real.exp (-(xiGamma γ *
        (circleAvg (h ω) ‖deriv ϕ z‖ 0 + Q γ * Real.log ‖deriv ϕ z‖)))) *
        (D (addFun (hbar ω) (Kt ω + jl))).internal (ball 0 (R / 2))
          (zoomMap ϕ z r u) (zoomMap ϕ z r v)) ∧
    (∀ᵐ ω ∂P, (D (h ω)).IsLength) := by
  set c : ℂ := deriv ϕ z with hcdef
  have hc0 : c ≠ 0 := hZ.deriv_ne_zero
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hh := hc.isWholePlaneGFF
  have hhb := hc.isWholePlaneGFF_bar
  have hc₀m : Measurable fun ω => -circleAvg (h ω) ‖c‖ 0 :=
    ((measurable_circleAvg_left ‖c‖ 0).comp hh.measurable).neg
  have hB : ball (0 : ℂ) (R / 2) ⊆ ball 0 R := ball_subset_ball (by linarith)
  have hB2 : ball (0 : ℂ) (R / 2) ⊆ closedBall 0 (2 * R) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  -- the local zoomed conformal neighbourhood
  have hVo : IsOpen (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) := by
    refine isOpen_image_conf isOpen_ball ?_ ?_
    · intro y hy
      have hy4 : y ∈ ball (0 : ℂ) (4 * R) := ball_subset_ball (by linarith) hy
      exact ((hZ.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hy4)).const_mul
        _).differentiableWithinAt
    · intro y hy y' hy' hyy
      rw [← zoomMap_zoomPsi hZ (hB2 hy), ← zoomMap_zoomPsi hZ (hB2 hy'), hyy]
  have hϕt : IsConfNbhd (zoomMap ϕ z r) (zoomSet z r W) (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) :=
    (hϕ.zoom z hr.ne').mono hVo hVt
  have himg : zoomMap ϕ z r '' (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) = ball 0 (R / 2) := by
    rw [image_image]
    exact (image_congr fun y hy => zoomMap_zoomPsi hZ (hB2 hy)).trans (image_id _)
  -- the fields
  have hg := isWholePlaneGFF_zoomDom hh hc0
  have hfm : Measurable fun ω => (Kt ω + jl) + ContinuousMap.const ℂ (Q γ * Real.log ‖c⁻¹‖) := by
    refine ContinuousMap.measurable_iff_eval.2 fun y => ?_
    have h1 : Measurable fun ω => Kt ω y := ContinuousMap.measurable_iff_eval.1 hKtm y
    simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
    exact (h1.add_const _).add_const _
  -- `D_h(c u, c v) = e^{ξ Q log|c|} D_{h(c ·)}(u, v)`
  have hcoord := GaussianLQG.IsCanonicalLQGMetric.ae_coord hD hh 0 hc0
  have hweyl_g := hD.1.ae_dist_addConst (isGFFPlusCont_of_wp hg)
  have hdist : ∀ᵐ ω ∂P, ∀ u v : ℂ, (D (zoomNorm c (h ω))).1 (u, v) =
      Real.exp (-(xiGamma γ * (circleAvg (h ω) ‖c‖ 0 + Q γ * Real.log ‖c‖))) *
        (D (h ω)).1 (c * u, c * v) := by
    filter_upwards [hcoord, hweyl_g] with ω h1 h2 u v
    have e1 : (D (h ω)).1 (c * u, c * v) =
        (D (addConst (zoomDom c (h ω)) (Q γ * Real.log ‖c‖))).1 (u, v) := by
      have := h1 u v
      rw [zero_add, zero_add] at this
      exact this
    rw [h2] at e1
    rw [zoomNorm, h2, e1, ← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  refine ⟨isNormalizedWPGFF_zoomNorm hh hc0, hhb.addConst hc₀m, hfm, ?_, hdist, ?_, ?_,
    hD.1.length P h (isGFFPlusCont_of_wp hh)⟩
  · -- the coupling
    filter_upwards [hc.coupling] with ω hω
    have hf' : ∀ y ∈ ball (0 : ℂ) (R / 2),
        ((Kt ω + jl) + ContinuousMap.const ℂ (Q γ * Real.log ‖c⁻¹‖)) y =
          K ω y + Q γ * Real.log ‖deriv (zoomPsi ϕ ψ z r) y‖ := by
      intro y hy
      have hyR := hB hy
      have hne := deriv_zoomExt_ne_zero hZ (by linarith) hyR
      simp only [ContinuousMap.add_apply, ContinuousMap.const_apply]
      rw [hKt ω y hy, hjl y hyR, deriv_zoomPsi hZ hR hyR, norm_mul,
        Real.log_mul (norm_ne_zero_iff.2 (inv_ne_zero hc0)) (norm_ne_zero_iff.2 hne)]
      ring
    have hcoup := isConfCoupling_of_nic hγ hϕ hψ hr hR hZ (by linarith) hVt hω (hKt ω) hf'
    exact hcoup.addConst hϕt _
  · -- the internal metric on `c⁻¹ B_{R/2}`
    filter_upwards [hdist] with ω hω u v
    set κ : ℝ := Real.exp (-(xiGamma γ * (circleAvg (h ω) ‖c‖ 0 + Q γ * Real.log ‖c‖)))
      with hκ
    have hκ0 : 0 < κ := Real.exp_pos _
    have hXY : ∀ x y : ℂ, (D (h ω)).1 (0 + c * x, 0 + c * y) =
        κ⁻¹ * (D (zoomNorm c (h ω))).1 (x, y) := fun x y => by
      rw [hω x y, zero_add, zero_add, ← mul_assoc, inv_mul_cancel₀ hκ0.ne', one_mul]
    have h1 := internal_affineC_preimage_eq hc0 0 (inv_pos.2 hκ0) hXY (ball 0 (R / 2)) u v
    simp only [zero_add] at h1
    rw [h1, ← mul_assoc, ← ENNReal.ofReal_mul hκ0.le, mul_inv_cancel₀ hκ0.ne',
      ENNReal.ofReal_one, one_mul]
  · -- the transported metric
    have hhbc := isGFFPlusCont_of_wp (hhb.addConst hc₀m)
    filter_upwards [ae_confMetric_add_const hD.1 hhbc,
      ae_confMetric_addConst hD.1 (isGFFPlusCont_of_wp hhb)] with ω h1 h2 u v
    rw [h1 _ _ _ hϕt, h2 _ _ _ hϕt, ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add, confMetric_def, himg]
    congr 3
    rw [norm_inv, Real.log_inv]
    ring

end SmallGammaGeodesics.CC
