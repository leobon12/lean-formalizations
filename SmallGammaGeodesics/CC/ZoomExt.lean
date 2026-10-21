import SmallGammaGeodesics.CC.PullbackZoom
import SmallGammaGeodesics.NIC.Transport
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Zoom and global near-identity extension (track CC, packet CC4; CC0 Details D6, deterministic part)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D6** (setup, Taylor bounds,
extension), for Gwynne–Miller arXiv:1905.00384 ([3]) §2 in the route S1 of CC0.

Let `IsConfNbhd ϕ W V`, let `ψ` be a left inverse of `ϕ` on `W`, let `Kc ⊆ V` be compact and `R > 0`.
For `z ∈ Kc` and small `r > 0` the **zoomed, derivative-normalized inverse map** is
`χ_{z,r}(y) = α_z⁻¹ r⁻¹ (ψ(ϕ z + r y) − z)` with `α_z = 1/ϕ'(z)` (`zoomInv`). Under the standing
hypotheses `ZoomHyp` (constants from `IsConfNbhd.exists_zoom_consts`, uniform in `z ∈ Kc`) it
satisfies on `B̄_{4R}` the Taylor bounds (`ZoomHyp.norm_sub_le`, `ZoomHyp.norm_deriv_sub_one_le`,
`ZoomHyp.norm_deriv_deriv_le`)
`|χ(y) − y| ≤ M₁M₂ r |y|²`, `|χ'(y) − 1| ≤ M₁M₂ r |y|`, `|χ''(y)| ≤ M₁M₂ r`,
with `M₁ = sup_{Kc} |ϕ'|` and `M₂ = sup |ψ''|` on a closed `δ`-neighbourhood of `ϕ(Kc)`.

The **global extension** is `Ξ = id + β_R (χ − id)` (`zoomExt`), with the radial cutoff
`β_R(y) = b(y/R)` (`zoomCut`; `b` a fixed `C^∞` bump, `= 1` on `B̄_1`, `= 0` off `B_2`). Then
`‖DΞ − I‖ ≤ M₁M₂(2 + 4M_b) R r` everywhere (`ZoomHyp.norm_fderiv_zoomExt_sub_le`); a `C^∞` map of `ℂ` with
`‖DΞ − I‖ ≤ ε ≤ 1/2` is a global diffeomorphism with `C^∞` inverse and `‖DΞ⁻¹ − I‖ ≤ 2ε`
(`exists_inverse_of_nearId`: `Ξ − id` is an `ε`-contraction, `ApproximatesLinearOn.toHomeomorph`, and
the inverse function theorem `Homeomorph.contDiff_symm`). `Ξ = χ` on `B̄_R`, `Ξ = id` off `B_{2R}`,
and `Ξ` is holomorphic on `B_R`, so `CC.IsNearIdDiffeo Ξ⁻¹ Ξ (ball 0 R) (C r)` holds
(`IsConfNbhd.exists_zoomExt`, packaged as `IsZoomExt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric

namespace SmallGammaGeodesics.CC

/-! ## The zoomed inverse map -/

/-- **The zoomed, derivative-normalized inverse map** `χ_{z,r}(y) = ϕ'(z) · r⁻¹ (ψ(ϕ z + r y) − z)`,
i.e. `α_z⁻¹ ψ_{z,r}(y)` with `α_z = 1/ϕ'(z)` and `ψ_{z,r}(y) = r⁻¹(ψ(ϕ(z) + r y) − z)` (CC0 D6). -/
def zoomInv (ϕ ψ : ℂ → ℂ) (z : ℂ) (r : ℝ) (y : ℂ) : ℂ :=
  deriv ϕ z * ((ψ (ϕ z + r * y) - z) / r)

theorem zoomInv_def (ϕ ψ : ℂ → ℂ) (z : ℂ) (r : ℝ) (y : ℂ) :
    zoomInv ϕ ψ z r y = deriv ϕ z * ((ψ (ϕ z + r * y) - z) / r) := rfl

/-- **Uniform constants for the zoom over a compact set** (CC0 D6, setup): a radius `δ > 0` with
`B̄(ϕ z, δ) ⊆ ϕ(W)` for `z ∈ Kc`, `M₁ ≥ sup_{Kc} |ϕ'|` and `M₂ ≥ sup |ψ''|` over these discs. -/
theorem IsConfNbhd.exists_zoom_consts {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V)
    (hψ : ∀ x ∈ W, ψ (ϕ x) = x) {Kc : Set ℂ} (hKc : IsCompact Kc) (hKcV : Kc ⊆ V) :
    ∃ δ M₁ M₂ : ℝ, 0 < δ ∧ 0 ≤ M₁ ∧ 0 ≤ M₂ ∧
      (∀ z ∈ Kc, closedBall (ϕ z) δ ⊆ ϕ '' W) ∧
      (∀ z ∈ Kc, ‖deriv ϕ z‖ ≤ M₁) ∧
      (∀ z ∈ Kc, ∀ x ∈ closedBall (ϕ z) δ, ‖deriv (deriv ψ) x‖ ≤ M₂) := by
  have hW := hϕ.isOpen_W
  have hd := hϕ.differentiableOn
  have hi := hϕ.injOn
  have hKcW : Kc ⊆ W := hKcV.trans hϕ.subset
  have hO : IsOpen (ϕ '' W) := isOpen_image_conf hW hd hi
  have hKimg : IsCompact (ϕ '' Kc) := hKc.image_of_continuousOn (hd.continuousOn.mono hKcW)
  obtain ⟨δ, hδ, hsub⟩ := hKimg.exists_cthickening_subset_open hO (image_mono hKcW)
  have hball : ∀ z ∈ Kc, closedBall (ϕ z) δ ⊆ cthickening δ (ϕ '' Kc) := fun z hz =>
    closedBall_subset_cthickening (mem_image_of_mem ϕ hz) δ
  obtain ⟨C₁, hC₁⟩ := hKc.exists_bound_of_continuousOn ((hd.deriv hW).continuousOn.mono hKcW)
  have hdψ : DifferentiableOn ℂ ψ (ϕ '' W) := differentiableOn_leftInv hW hd hi hψ
  have hddψ : DifferentiableOn ℂ (deriv (deriv ψ)) (ϕ '' W) := (hdψ.deriv hO).deriv hO
  obtain ⟨C₂, hC₂⟩ := (hKimg.cthickening (r := δ)).exists_bound_of_continuousOn
    (hddψ.continuousOn.mono hsub)
  refine ⟨δ, max C₁ 0, max C₂ 0, hδ, le_max_right _ _, le_max_right _ _,
    fun z hz => (hball z hz).trans hsub, fun z hz => (hC₁ z hz).trans (le_max_left _ _),
    fun z hz x hx => (hC₂ x (hball z hz hx)).trans (le_max_left _ _)⟩

/-- **Uniform two-sided bounds on `|ϕ'|` over a compact set** (compactness and injectivity). -/
theorem IsConfNbhd.exists_deriv_bounds {ϕ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V)
    {Kc : Set ℂ} (hKc : IsCompact Kc) (hKcV : Kc ⊆ V) :
    ∃ m M : ℝ, 0 < m ∧ ∀ z ∈ Kc, m ≤ ‖deriv ϕ z‖ ∧ ‖deriv ϕ z‖ ≤ M := by
  have hW := hϕ.isOpen_W
  have hd := hϕ.differentiableOn
  have hKcW : Kc ⊆ W := hKcV.trans hϕ.subset
  have hc : ContinuousOn (fun z => ‖deriv ϕ z‖) Kc :=
    ((hd.deriv hW).continuousOn.mono hKcW).norm
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn ((hd.deriv hW).continuousOn.mono hKcW)
  rcases Kc.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, M, one_pos, fun z hz => by simp [hKe] at hz⟩
  obtain ⟨z₀, hz₀, hmin⟩ := hKc.exists_isMinOn hKne hc
  have hne : deriv ϕ z₀ ≠ 0 :=
    QuantumZipper.CA.deriv_ne_zero_of_injOn hW hd hϕ.injOn (hKcW hz₀)
  refine ⟨‖deriv ϕ z₀‖, M, norm_pos_iff.2 hne, fun z hz => ⟨hmin hz, hM z hz⟩⟩

section ZoomInv

variable {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} {z : ℂ} {r δ M₁ M₂ ρ : ℝ}

/-- the affine point `ϕ z + r y` lies in `B̄(ϕ z, δ)` when `r ‖y‖ ≤ r ρ ≤ δ` -/
theorem zoomAff_mem_closedBall (hr : 0 < r) (hrρ : r * ρ ≤ δ) {y : ℂ} (hy : ‖y‖ ≤ ρ) :
    ϕ z + (r : ℂ) * y ∈ closedBall (ϕ z) δ := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hr]
  exact (mul_le_mul_of_nonneg_left hy hr.le).trans hrρ

/-- `χ_{z,r}(0) = 0` -/
theorem zoomInv_zero (hψ : ∀ x ∈ W, ψ (ϕ x) = x) (hz : z ∈ W) : zoomInv ϕ ψ z r 0 = 0 := by
  rw [zoomInv_def, mul_zero, add_zero, hψ z hz, sub_self, zero_div, mul_zero]

/-- `χ'_{z,r}(y) = ϕ'(z) ψ'(ϕ z + r y)` wherever `ϕ z + r y ∈ ϕ(W)` -/
theorem hasDerivAt_zoomInv (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ x ∈ W, ψ (ϕ x) = x) (hr : 0 < r)
    {y : ℂ} (hy : ϕ z + (r : ℂ) * y ∈ ϕ '' W) :
    HasDerivAt (zoomInv ϕ ψ z r) (deriv ϕ z * deriv ψ (ϕ z + r * y)) y := by
  have hW := hϕ.isOpen_W
  have hd := hϕ.differentiableOn
  have hi := hϕ.injOn
  have hO : IsOpen (ϕ '' W) := isOpen_image_conf hW hd hi
  have hdψ : DifferentiableOn ℂ ψ (ϕ '' W) := differentiableOn_leftInv hW hd hi hψ
  have h1 : HasDerivAt (fun y : ℂ => ϕ z + (r : ℂ) * y) (r : ℂ) y := by
    simpa using ((hasDerivAt_id y).const_mul (r : ℂ)).const_add (ϕ z)
  have h2 : HasDerivAt ψ (deriv ψ (ϕ z + r * y)) (ϕ z + r * y) :=
    (hdψ.differentiableAt (hO.mem_nhds hy)).hasDerivAt
  have h3 : HasDerivAt (fun y : ℂ => ψ (ϕ z + (r : ℂ) * y)) (deriv ψ (ϕ z + r * y) * r) y :=
    h2.comp y h1
  have h4 := ((h3.sub_const z).div_const (r : ℂ)).const_mul (deriv ϕ z)
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have e : deriv ϕ z * (deriv ψ (ϕ z + r * y) * r / r) = deriv ϕ z * deriv ψ (ϕ z + r * y) := by
    rw [mul_div_cancel_right₀ _ hr0]
  rw [e] at h4
  exact h4

/-- `ϕ'(z) ψ'(ϕ z) = 1` -/
theorem deriv_mul_deriv_leftInv_self (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ x ∈ W, ψ (ϕ x) = x)
    (hz : z ∈ W) : deriv ϕ z * deriv ψ (ϕ z) = 1 := by
  rw [mul_comm]
  exact deriv_leftInv_mul hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ hz

/-- **Taylor bound for `χ'`**: `|ϕ'(z) ψ'(ϕ z + r y) − 1| ≤ M₁M₂ r |y|` for `|y| ≤ ρ`. -/
theorem norm_deriv_zoomInv_sub_one_le (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ x ∈ W, ψ (ϕ x) = x)
    (hz : z ∈ W) (hball : closedBall (ϕ z) δ ⊆ ϕ '' W) (hM₁ : ‖deriv ϕ z‖ ≤ M₁)
    (hM₂ : ∀ x ∈ closedBall (ϕ z) δ, ‖deriv (deriv ψ) x‖ ≤ M₂) (hM₁0 : 0 ≤ M₁) (hr : 0 < r)
    (hrρ : r * ρ ≤ δ) {y : ℂ} (hy : ‖y‖ ≤ ρ) :
    ‖deriv ϕ z * deriv ψ (ϕ z + r * y) - 1‖ ≤ M₁ * M₂ * r * ‖y‖ := by
  have hW := hϕ.isOpen_W
  have hd := hϕ.differentiableOn
  have hi := hϕ.injOn
  have hO : IsOpen (ϕ '' W) := isOpen_image_conf hW hd hi
  have hdψ' : DifferentiableOn ℂ (deriv ψ) (ϕ '' W) :=
    (differentiableOn_leftInv hW hd hi hψ).deriv hO
  have hmem := zoomAff_mem_closedBall (ϕ := ϕ) (z := z) hr hrρ hy
  have hδ0 : 0 ≤ δ := le_trans (by positivity) (dist_nonneg.trans (mem_closedBall.1 hmem))
  have hmvt : ‖deriv ψ (ϕ z + r * y) - deriv ψ (ϕ z)‖ ≤ M₂ * ‖ϕ z + r * y - ϕ z‖ :=
    (convex_closedBall (ϕ z) δ).norm_image_sub_le_of_norm_deriv_le
      (fun x hx => hdψ'.differentiableAt (hO.mem_nhds (hball hx))) hM₂
      (mem_closedBall_self hδ0) hmem
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ (ϕ z) (mem_closedBall_self hδ0))
  have e1 : deriv ϕ z * deriv ψ (ϕ z + r * y) - 1 =
      deriv ϕ z * (deriv ψ (ϕ z + r * y) - deriv ψ (ϕ z)) := by
    rw [mul_sub, deriv_mul_deriv_leftInv_self hϕ hψ hz]
  have e2 : ‖ϕ z + (r : ℂ) * y - ϕ z‖ = r * ‖y‖ := by
    rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [e1, norm_mul]
  calc ‖deriv ϕ z‖ * ‖deriv ψ (ϕ z + r * y) - deriv ψ (ϕ z)‖
      ≤ M₁ * (M₂ * (r * ‖y‖)) := by
        rw [← e2]; exact mul_le_mul hM₁ hmvt (norm_nonneg _) hM₁0
    _ = M₁ * M₂ * r * ‖y‖ := by ring

end ZoomInv

/-! ## The cutoff `β_R` -/

/-- the fixed bump `b`: `C^∞`, `= 1` on `B̄_1`, `= 0` off `B_2`, values in `[0, 1]` -/
def zoomBump : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- **the radial cutoff** `β_R(y) = b(y/R)`: `= 1` on `B̄_R`, `= 0` off `B_{2R}` -/
def zoomCut (R : ℝ) (y : ℂ) : ℝ := zoomBump (R⁻¹ • y)

theorem contDiff_zoomCut (R : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (zoomCut R) :=
  zoomBump.contDiff.comp (contDiff_id.const_smul R⁻¹)

theorem zoomCut_nonneg (R : ℝ) (y : ℂ) : 0 ≤ zoomCut R y := zoomBump.nonneg

theorem zoomCut_le_one (R : ℝ) (y : ℂ) : zoomCut R y ≤ 1 := zoomBump.le_one

private theorem norm_inv_smul {R : ℝ} (hR : 0 < R) (y : ℂ) : ‖R⁻¹ • y‖ = ‖y‖ / R := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR), inv_mul_eq_div]

theorem zoomCut_eq_one {R : ℝ} (hR : 0 < R) {y : ℂ} (hy : ‖y‖ ≤ R) : zoomCut R y = 1 := by
  refine zoomBump.one_of_mem_closedBall ?_
  show R⁻¹ • y ∈ closedBall (0 : ℂ) 1
  rw [mem_closedBall, dist_zero_right, norm_inv_smul hR, div_le_one hR]
  exact hy

theorem zoomCut_eq_zero {R : ℝ} (hR : 0 < R) {y : ℂ} (hy : 2 * R ≤ ‖y‖) : zoomCut R y = 0 := by
  refine zoomBump.zero_of_le_dist ?_
  show (2 : ℝ) ≤ dist (R⁻¹ • y) 0
  rw [dist_zero_right, norm_inv_smul hR, le_div_iff₀ hR]
  exact hy

/-- `β_R = 0` near every point with `‖y‖ > 2R` -/
theorem zoomCut_eventuallyEq_zero {R : ℝ} (hR : 0 < R) {y : ℂ} (hy : 2 * R < ‖y‖) :
    zoomCut R =ᶠ[𝓝 y] fun _ => 0 :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hy)
    fun _w hw => zoomCut_eq_zero hR (le_of_lt hw)

/-- `‖Dβ_R‖ ≤ M_b / R` -/
theorem exists_norm_fderiv_zoomCut_le : ∃ Mb : ℝ, 0 ≤ Mb ∧ ∀ R : ℝ, 0 < R → ∀ y : ℂ,
    ‖fderiv ℝ (zoomCut R) y‖ ≤ Mb / R := by
  have hb : ContDiff ℝ 1 (zoomBump : ℂ → ℝ) := zoomBump.contDiff
  have hcont : Continuous (fderiv ℝ (zoomBump : ℂ → ℝ)) := hb.continuous_fderiv one_ne_zero
  have hsupp : HasCompactSupport (fderiv ℝ (zoomBump : ℂ → ℝ)) :=
    zoomBump.hasCompactSupport.fderiv ℝ
  obtain ⟨M, hM⟩ := hcont.bounded_above_of_compact_support hsupp
  have hLip : LipschitzWith M.toNNReal (zoomBump : ℂ → ℝ) :=
    lipschitzWith_of_nnnorm_fderiv_le (hb.differentiable one_ne_zero) fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
      exact (hM x).trans (le_max_left _ _)
  refine ⟨max M 0, le_max_right _ _, fun R hR y => ?_⟩
  have hLip2 : LipschitzWith (M.toNNReal * ‖R⁻¹‖₊) (zoomCut R) :=
    hLip.comp (lipschitzWith_smul R⁻¹)
  have h := norm_fderiv_le_of_lipschitz ℝ (x₀ := y) hLip2
  have e : ((M.toNNReal * ‖R⁻¹‖₊ : NNReal) : ℝ) = max M 0 / R := by
    rw [NNReal.coe_mul, coe_nnnorm, Real.coe_toNNReal', Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hR), div_eq_mul_inv]
  rwa [e] at h

/-! ## Standing hypotheses at one centre and scale -/

/-- The standing hypotheses of CC0 D6 at one centre `z` and scale `r` (with the zoomed radius
`4R`): `ϕ z + r B̄_{4R} ⊆ B̄(ϕ z, δ) ⊆ ϕ(W)`, `|ϕ'(z)| ≤ M₁` and `|ψ''| ≤ M₂` on `B̄(ϕ z, δ)`. -/
structure ZoomHyp (ϕ ψ : ℂ → ℂ) (W V : Set ℂ) (z : ℂ) (r R δ M₁ M₂ : ℝ) : Prop where
  conf : IsConfNbhd ϕ W V
  leftInv : ∀ x ∈ W, ψ (ϕ x) = x
  mem : z ∈ W
  ball_sub : closedBall (ϕ z) δ ⊆ ϕ '' W
  deriv_le : ‖deriv ϕ z‖ ≤ M₁
  deriv2_le : ∀ x ∈ closedBall (ϕ z) δ, ‖deriv (deriv ψ) x‖ ≤ M₂
  M₁_nonneg : 0 ≤ M₁
  M₂_nonneg : 0 ≤ M₂
  r_pos : 0 < r
  R_pos : 0 < R
  small : r * (4 * R) ≤ δ

namespace ZoomHyp

variable {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} {z : ℂ} {r R δ M₁ M₂ : ℝ}
  (H : ZoomHyp ϕ ψ W V z r R δ M₁ M₂)
include H

theorem aff_mem {y : ℂ} (hy : ‖y‖ ≤ 4 * R) : ϕ z + (r : ℂ) * y ∈ ϕ '' W :=
  H.ball_sub (zoomAff_mem_closedBall H.r_pos H.small hy)

theorem hasDerivAt {y : ℂ} (hy : ‖y‖ ≤ 4 * R) :
    HasDerivAt (zoomInv ϕ ψ z r) (deriv ϕ z * deriv ψ (ϕ z + r * y)) y :=
  hasDerivAt_zoomInv H.conf H.leftInv H.r_pos (H.aff_mem hy)

theorem deriv_eq {y : ℂ} (hy : ‖y‖ ≤ 4 * R) :
    deriv (zoomInv ϕ ψ z r) y = deriv ϕ z * deriv ψ (ϕ z + r * y) :=
  (H.hasDerivAt hy).deriv

theorem differentiableOn : DifferentiableOn ℂ (zoomInv ϕ ψ z r) (ball 0 (4 * R)) := fun _y hy =>
  (H.hasDerivAt (le_of_lt (mem_ball_zero_iff.1 hy))).differentiableAt.differentiableWithinAt

/-- **Taylor bound** `|χ'(y) − 1| ≤ M₁M₂ r |y|` on `B̄_{4R}` -/
theorem norm_deriv_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 4 * R) :
    ‖deriv (zoomInv ϕ ψ z r) y - 1‖ ≤ M₁ * M₂ * r * ‖y‖ := by
  rw [H.deriv_eq hy]
  exact norm_deriv_zoomInv_sub_one_le H.conf H.leftInv H.mem H.ball_sub H.deriv_le H.deriv2_le
    H.M₁_nonneg H.r_pos H.small hy

/-- **Taylor bound** `|χ(y) − y| ≤ M₁M₂ r |y|²` on `B̄_{4R}` -/
theorem norm_sub_le {y : ℂ} (hy : ‖y‖ ≤ 4 * R) :
    ‖zoomInv ϕ ψ z r y - y‖ ≤ M₁ * M₂ * r * ‖y‖ ^ 2 := by
  set F : ℂ → ℂ := fun w => zoomInv ϕ ψ z r w - w with hF
  have hderF : ∀ w ∈ closedBall (0 : ℂ) ‖y‖,
      HasDerivAt F (deriv ϕ z * deriv ψ (ϕ z + r * w) - 1) w := fun w hw => by
    have hw' : ‖w‖ ≤ 4 * R := (mem_closedBall_zero_iff.1 hw).trans hy
    exact (H.hasDerivAt hw').sub (hasDerivAt_id w)
  have hbd : ∀ w ∈ closedBall (0 : ℂ) ‖y‖, ‖deriv F w‖ ≤ M₁ * M₂ * r * ‖y‖ := fun w hw => by
    have hw0 : ‖w‖ ≤ ‖y‖ := mem_closedBall_zero_iff.1 hw
    rw [(hderF w hw).deriv]
    refine (norm_deriv_zoomInv_sub_one_le H.conf H.leftInv H.mem H.ball_sub H.deriv_le H.deriv2_le
      H.M₁_nonneg H.r_pos H.small (hw0.trans hy)).trans ?_
    have h0 : 0 ≤ M₁ * M₂ * r := by
      have := H.r_pos; have := H.M₁_nonneg; have := H.M₂_nonneg; positivity
    exact mul_le_mul_of_nonneg_left hw0 h0
  have hmvt := (convex_closedBall (0 : ℂ) ‖y‖).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => (hderF w hw).differentiableAt) hbd (mem_closedBall_self (norm_nonneg y))
    (mem_closedBall_zero_iff.2 le_rfl)
  have hF0 : F 0 = 0 := by
    simp only [hF, zoomInv_zero H.leftInv H.mem, sub_zero]
  rw [hF0, sub_zero, sub_zero] at hmvt
  calc ‖zoomInv ϕ ψ z r y - y‖ = ‖F y‖ := rfl
    _ ≤ M₁ * M₂ * r * ‖y‖ * ‖y‖ := hmvt
    _ = M₁ * M₂ * r * ‖y‖ ^ 2 := by ring

/-- **Taylor bound** `|χ''(y)| ≤ M₁M₂ r` on `B_{4R}` -/
theorem norm_deriv_deriv_le {y : ℂ} (hy : ‖y‖ < 4 * R) :
    ‖deriv (deriv (zoomInv ϕ ψ z r)) y‖ ≤ M₁ * M₂ * r := by
  have hW := H.conf.isOpen_W
  have hd := H.conf.differentiableOn
  have hi := H.conf.injOn
  have hO : IsOpen (ϕ '' W) := isOpen_image_conf hW hd hi
  have hdψ' : DifferentiableOn ℂ (deriv ψ) (ϕ '' W) :=
    (differentiableOn_leftInv hW hd hi H.leftInv).deriv hO
  have hev : deriv (zoomInv ϕ ψ z r) =ᶠ[𝓝 y] fun w => deriv ϕ z * deriv ψ (ϕ z + r * w) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy)) fun w hw =>
      H.deriv_eq (le_of_lt (mem_ball_zero_iff.1 hw))
  have hmem := H.aff_mem (le_of_lt hy)
  have h1 : HasDerivAt (fun w : ℂ => ϕ z + (r : ℂ) * w) (r : ℂ) y := by
    simpa using ((hasDerivAt_id y).const_mul (r : ℂ)).const_add (ϕ z)
  have h2 : HasDerivAt (deriv ψ) (deriv (deriv ψ) (ϕ z + r * y)) (ϕ z + r * y) :=
    (hdψ'.differentiableAt (hO.mem_nhds hmem)).hasDerivAt
  have h3a : HasDerivAt (fun w : ℂ => deriv ψ (ϕ z + (r : ℂ) * w))
      (deriv (deriv ψ) (ϕ z + r * y) * r) y := by
    have := HasDerivAt.comp y h2 h1
    simpa only [Function.comp_def] using this
  have h3 : HasDerivAt (fun w : ℂ => deriv ϕ z * deriv ψ (ϕ z + (r : ℂ) * w))
      (deriv ϕ z * (deriv (deriv ψ) (ϕ z + r * y) * r)) y := h3a.const_mul (deriv ϕ z)
  rw [hev.deriv_eq, h3.deriv, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos H.r_pos]
  have hM₂ : ‖deriv (deriv ψ) (ϕ z + r * y)‖ ≤ M₂ :=
    H.deriv2_le _ (zoomAff_mem_closedBall H.r_pos H.small (le_of_lt hy))
  calc ‖deriv ϕ z‖ * (‖deriv (deriv ψ) (ϕ z + r * y)‖ * r) ≤ M₁ * (M₂ * r) :=
        mul_le_mul H.deriv_le (mul_le_mul_of_nonneg_right hM₂ H.r_pos.le)
          (by have := H.r_pos; positivity) H.M₁_nonneg
    _ = M₁ * M₂ * r := by ring

/-- `ϕ'(z) ≠ 0` -/
theorem deriv_ne_zero : deriv ϕ z ≠ 0 := by
  intro h0
  have := deriv_mul_deriv_leftInv_self H.conf H.leftInv H.mem
  rw [h0, zero_mul] at this
  exact zero_ne_one this

/-- `α_z χ(y) = r⁻¹ (ψ(ϕ z + r y) − z)` -/
theorem inv_deriv_mul_zoomInv (y : ℂ) :
    (deriv ϕ z)⁻¹ * zoomInv ϕ ψ z r y = (ψ (ϕ z + r * y) - z) / r := by
  rw [zoomInv_def, ← mul_assoc, inv_mul_cancel₀ H.deriv_ne_zero, one_mul]

/-- `z + r α_z χ(y) = ψ(ϕ z + r y)` -/
theorem zoomAff_inv_deriv_mul_zoomInv (y : ℂ) :
    z + (r : ℂ) * ((deriv ϕ z)⁻¹ * zoomInv ϕ ψ z r y) = ψ (ϕ z + r * y) := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 H.r_pos.ne'
  rw [H.inv_deriv_mul_zoomInv, mul_div_cancel₀ _ hr0, add_sub_cancel]

/-- the link with the zoomed map: `α_z χ(y) ∈ r⁻¹(W − z)` -/
theorem mem_zoomSet {y : ℂ} (hy : ‖y‖ ≤ 4 * R) :
    (deriv ϕ z)⁻¹ * zoomInv ϕ ψ z r y ∈ zoomSet z r W := by
  rw [CC.mem_zoomSet, H.zoomAff_inv_deriv_mul_zoomInv]
  exact leftInv_mem H.leftInv (H.aff_mem hy)

/-- the link with the zoomed map: `ϕ̃(α_z χ(y)) = y`, `ϕ̃ = zoomMap ϕ z r` -/
theorem zoomMap_eq {y : ℂ} (hy : ‖y‖ ≤ 4 * R) :
    zoomMap ϕ z r ((deriv ϕ z)⁻¹ * zoomInv ϕ ψ z r y) = y := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 H.r_pos.ne'
  rw [zoomMap, H.zoomAff_inv_deriv_mul_zoomInv, apply_leftInv H.leftInv (H.aff_mem hy),
    add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hr0, one_mul]

end ZoomHyp

/-! ## The global extension `Ξ` -/

/-- **The global extension** `Ξ = id + β_R (χ_{z,r} − id)` of `χ_{z,r}` from `B̄_R` (CC0 D6):
`Ξ = χ_{z,r}` on `B̄_R` and `Ξ = id` off `B_{2R}`. -/
def zoomExt (ϕ ψ : ℂ → ℂ) (z : ℂ) (r R : ℝ) (y : ℂ) : ℂ :=
  y + zoomCut R y • (zoomInv ϕ ψ z r y - y)

theorem zoomExt_def (ϕ ψ : ℂ → ℂ) (z : ℂ) (r R : ℝ) (y : ℂ) :
    zoomExt ϕ ψ z r R y = y + zoomCut R y • (zoomInv ϕ ψ z r y - y) := rfl

section ZoomExt

variable {ϕ ψ : ℂ → ℂ} {z : ℂ} {r R : ℝ}

/-- `Ξ = id` off `B_{2R}` -/
theorem zoomExt_eq_self (hR : 0 < R) {y : ℂ} (hy : 2 * R ≤ ‖y‖) : zoomExt ϕ ψ z r R y = y := by
  rw [zoomExt_def, zoomCut_eq_zero hR hy, zero_smul, add_zero]

/-- `Ξ = id` near every point with `‖y‖ > 2R` -/
theorem zoomExt_eventuallyEq_self (hR : 0 < R) {y : ℂ} (hy : 2 * R < ‖y‖) :
    zoomExt ϕ ψ z r R =ᶠ[𝓝 y] id :=
  Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_norm).mem_nhds hy)
    fun _w hw => zoomExt_eq_self hR (le_of_lt hw)

/-- `Ξ = χ_{z,r}` on `B̄_R` -/
theorem zoomExt_eq_zoomInv (hR : 0 < R) {y : ℂ} (hy : ‖y‖ ≤ R) :
    zoomExt ϕ ψ z r R y = zoomInv ϕ ψ z r y := by
  rw [zoomExt_def, zoomCut_eq_one hR hy, one_smul, add_sub_cancel]

end ZoomExt

namespace ZoomHyp

variable {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} {z : ℂ} {r R δ M₁ M₂ : ℝ}
  (H : ZoomHyp ϕ ψ W V z r R δ M₁ M₂)
include H

/-- `|Ξ(y) − y| ≤ 4 M₁M₂ R² r` everywhere -/
theorem norm_zoomExt_sub_le (y : ℂ) : ‖zoomExt ϕ ψ z r R y - y‖ ≤ 4 * M₁ * M₂ * R ^ 2 * r := by
  have h0 : 0 ≤ M₁ * M₂ * r := by
    have := H.r_pos; have := H.M₁_nonneg; have := H.M₂_nonneg; positivity
  rw [zoomExt_def, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (zoomCut_nonneg R y)]
  by_cases hy : ‖y‖ ≤ 2 * R
  · have hy4 : ‖y‖ ≤ 4 * R := by linarith [H.R_pos]
    calc zoomCut R y * ‖zoomInv ϕ ψ z r y - y‖ ≤ 1 * (M₁ * M₂ * r * ‖y‖ ^ 2) :=
          mul_le_mul (zoomCut_le_one R y) (H.norm_sub_le hy4) (norm_nonneg _) zero_le_one
      _ ≤ 1 * (M₁ * M₂ * r * (2 * R) ^ 2) := by
          rw [one_mul, one_mul]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy 2) h0
      _ = 4 * M₁ * M₂ * R ^ 2 * r := by ring
  · rw [zoomCut_eq_zero H.R_pos (le_of_lt (not_le.1 hy)), zero_mul]
    have : 0 ≤ M₁ * M₂ * r * R ^ 2 := mul_nonneg h0 (sq_nonneg R)
    linarith

/-- `Ξ` is `C^∞` -/
theorem contDiff_zoomExt : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (zoomExt ϕ ψ z r R) := by
  have hχ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (zoomInv ϕ ψ z r) (ball 0 (4 * R)) :=
    (H.differentiableOn.contDiffOn isOpen_ball).restrict_scalars ℝ
  have hon : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (zoomExt ϕ ψ z r R) (ball 0 (4 * R)) :=
    contDiffOn_id.add ((contDiff_zoomCut R).contDiffOn.smul (hχ.sub contDiffOn_id))
  refine contDiff_iff_contDiffAt.2 fun y => ?_
  by_cases hy : ‖y‖ < 4 * R
  · exact hon.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy))
  · have hy' : 2 * R < ‖y‖ := by linarith [not_lt.1 hy, H.R_pos]
    exact contDiffAt_id.congr_of_eventuallyEq (zoomExt_eventuallyEq_self H.R_pos hy')

/-- **`‖DΞ − I‖ ≤ M₁M₂(2 + 4M_b) R r` everywhere** (CC0 D6, with `‖Dβ_R‖ ≤ M_b/R`) -/
theorem norm_fderiv_zoomExt_sub_le {Mb : ℝ} (hMb0 : 0 ≤ Mb)
    (hMb : ∀ y, ‖fderiv ℝ (zoomCut R) y‖ ≤ Mb / R) (y : ℂ) :
    ‖fderiv ℝ (zoomExt ϕ ψ z r R) y - ContinuousLinearMap.id ℝ ℂ‖ ≤
      M₁ * M₂ * (2 + 4 * Mb) * R * r := by
  have hR := H.R_pos
  have hr := H.r_pos
  have hM₁ := H.M₁_nonneg
  have hM₂ := H.M₂_nonneg
  have hbd0 : 0 ≤ M₁ * M₂ * (2 + 4 * Mb) * R * r := by positivity
  by_cases hy : ‖y‖ ≤ 2 * R
  · have hy4 : ‖y‖ ≤ 4 * R := by linarith
    set c : ℂ := deriv ϕ z * deriv ψ (ϕ z + r * y) with hc
    have hχ : HasFDerivAt (zoomInv ϕ ψ z r)
        ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ) y :=
      (H.hasDerivAt hy4).hasFDerivAt.restrictScalars ℝ
    have hβ : HasFDerivAt (zoomCut R) (fderiv ℝ (zoomCut R) y) y :=
      ((contDiff_zoomCut R).differentiable (by simp)).differentiableAt.hasFDerivAt
    have hΞ : HasFDerivAt (zoomExt ϕ ψ z r R)
        (ContinuousLinearMap.id ℝ ℂ + (zoomCut R y • (((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ) -
          ContinuousLinearMap.id ℝ ℂ) + (fderiv ℝ (zoomCut R) y).smulRight
            (zoomInv ϕ ψ z r y - y))) y :=
      (hasFDerivAt_id y).add (hβ.smul (hχ.sub (hasFDerivAt_id y)))
    rw [hΞ.fderiv, add_sub_cancel_left]
    refine ContinuousLinearMap.opNorm_le_bound _ hbd0 fun v => ?_
    have happ : ((zoomCut R y • (((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ) -
          ContinuousLinearMap.id ℝ ℂ) + (fderiv ℝ (zoomCut R) y).smulRight
            (zoomInv ϕ ψ z r y - y)) : ℂ →L[ℝ] ℂ) v =
        zoomCut R y • ((c - 1) * v) + (fderiv ℝ (zoomCut R) y v) • (zoomInv ϕ ψ z r y - y) := by
      simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.coe_restrictScalars',
        ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul]
      rw [show v * c - v = (c - 1) * v by ring]
    rw [happ]
    have hc1 : ‖c - 1‖ ≤ M₁ * M₂ * r * (2 * R) :=
      (norm_deriv_zoomInv_sub_one_le H.conf H.leftInv H.mem H.ball_sub H.deriv_le H.deriv2_le
        H.M₁_nonneg H.r_pos H.small hy4).trans
        (mul_le_mul_of_nonneg_left hy (by positivity))
    have hχy : ‖zoomInv ϕ ψ z r y - y‖ ≤ M₁ * M₂ * r * (2 * R) ^ 2 :=
      (H.norm_sub_le hy4).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hy 2) (by positivity))
    have hDβ : ‖fderiv ℝ (zoomCut R) y v‖ ≤ Mb / R * ‖v‖ :=
      ((fderiv ℝ (zoomCut R) y).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hMb y) (norm_nonneg v))
    have hβ1 : ‖zoomCut R y‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (zoomCut_nonneg R y)]; exact zoomCut_le_one R y
    calc ‖zoomCut R y • ((c - 1) * v) + (fderiv ℝ (zoomCut R) y v) • (zoomInv ϕ ψ z r y - y)‖
        ≤ ‖zoomCut R y • ((c - 1) * v)‖ + ‖(fderiv ℝ (zoomCut R) y v) • (zoomInv ϕ ψ z r y - y)‖ :=
          norm_add_le _ _
      _ = ‖zoomCut R y‖ * (‖c - 1‖ * ‖v‖) +
            ‖fderiv ℝ (zoomCut R) y v‖ * ‖zoomInv ϕ ψ z r y - y‖ := by
          rw [norm_smul, norm_smul, norm_mul]
      _ ≤ 1 * (M₁ * M₂ * r * (2 * R) * ‖v‖) + Mb / R * ‖v‖ * (M₁ * M₂ * r * (2 * R) ^ 2) := by
          gcongr
      _ = M₁ * M₂ * (2 + 4 * Mb) * R * r * ‖v‖ := by
          field_simp
          ring
  · have hy' : 2 * R < ‖y‖ := not_le.1 hy
    rw [(zoomExt_eventuallyEq_self (ϕ := ϕ) (ψ := ψ) (z := z) (r := r) hR hy').fderiv_eq,
      fderiv_id, sub_self, norm_zero]
    exact hbd0

/-- `Ξ` is holomorphic on `B_R` (where it equals `χ_{z,r}`) -/
theorem differentiableOn_zoomExt : DifferentiableOn ℂ (zoomExt ϕ ψ z r R) (ball 0 R) :=
  fun y hy => by
    have hy' : ‖y‖ < R := mem_ball_zero_iff.1 hy
    have hev : zoomExt ϕ ψ z r R =ᶠ[𝓝 y] zoomInv ϕ ψ z r :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) fun w hw =>
        zoomExt_eq_zoomInv H.R_pos (le_of_lt (mem_ball_zero_iff.1 hw))
    exact ((H.hasDerivAt (by linarith [H.R_pos])).differentiableAt.congr_of_eventuallyEq
      hev).differentiableWithinAt

end ZoomHyp

/-! ## Near-identity maps are global diffeomorphisms -/

/-- **A `C^∞` near-identity map of `ℂ` is a `C^∞` diffeomorphism.** If `‖DΞ − I‖ ≤ ε ≤ 1/2`
everywhere, then `Ξ − id` is an `ε`-contraction, so `Ξ` is a homeomorphism
(`ApproximatesLinearOn.toHomeomorph`); its inverse is `C^∞` by the inverse function theorem
(`Homeomorph.contDiff_symm`, `DΞ = I + (DΞ − I)` invertible by the Neumann series), and
`‖DΞ⁻¹ − I‖ ≤ 2ε` (`NIC.norm_sub_id_le_of_comp_eq_id`). -/
theorem exists_inverse_of_nearId {Ξ : ℂ → ℂ} {ε : ℝ}
    (hΞ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ξ) (hε : ε ≤ 1 / 2)
    (hD : ∀ y, ‖fderiv ℝ Ξ y - ContinuousLinearMap.id ℝ ℂ‖ ≤ ε) :
    ∃ Ξinv : ℂ → ℂ, (∀ x, Ξ (Ξinv x) = x) ∧ (∀ y, Ξinv (Ξ y) = y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ξinv ∧
      ∀ x, ‖fderiv ℝ Ξinv x - ContinuousLinearMap.id ℝ ℂ‖ ≤ 2 * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hD 0)
  have hdiff : Differentiable ℝ Ξ := hΞ.differentiable (by simp)
  set g : ℂ → ℂ := fun y => Ξ y - y with hg
  have hgd : Differentiable ℝ g := hdiff.sub differentiable_id
  have hgD : ∀ y, fderiv ℝ g y = fderiv ℝ Ξ y - ContinuousLinearMap.id ℝ ℂ := fun y =>
    ((hdiff y).hasFDerivAt.sub (hasFDerivAt_id y)).fderiv
  have hLip : LipschitzWith ε.toNNReal g :=
    lipschitzWith_of_nnnorm_fderiv_le hgd fun y => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hε0, hgD]
      exact hD y
  have hA : ApproximatesLinearOn Ξ
      ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) univ ε.toNNReal := by
    intro x _ y _
    have h := hLip.dist_le_mul x y
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hε0] at h
    have e : Ξ x - Ξ y - ((ContinuousLinearEquiv.refl ℝ ℂ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) (x - y) =
        g x - g y := by
      simp only [hg, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.refl_apply]
      ring
    rw [e, Real.coe_toNNReal _ hε0]
    exact h
  have hnorm1 : ‖((ContinuousLinearEquiv.refl ℝ ℂ).symm : ℂ →L[ℝ] ℂ)‖₊ = 1 := by simp
  have hc : Subsingleton ℂ ∨
      ε.toNNReal < ‖((ContinuousLinearEquiv.refl ℝ ℂ).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    right
    rw [hnorm1, inv_one, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hε0, NNReal.coe_one]
    linarith
  set H := hA.toHomeomorph Ξ hc with hH
  have hHcoe : (H : ℂ → ℂ) = Ξ := rfl
  have hnorm : ∀ a, ‖-(fderiv ℝ g a)‖ < 1 := fun a => by
    rw [norm_neg, hgD]; linarith [hD a]
  have hsymm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (H.symm : ℂ → ℂ) := by
    refine H.contDiff_symm
      (f₀' := fun a => ContinuousLinearEquiv.unitsEquiv ℝ ℂ (Units.oneSub _ (hnorm a)))
      (fun a => ?_) hΞ
    have e : ((ContinuousLinearEquiv.unitsEquiv ℝ ℂ (Units.oneSub _ (hnorm a)) : ℂ ≃L[ℝ] ℂ) :
        ℂ →L[ℝ] ℂ) = fderiv ℝ Ξ a := by
      ext1 v
      rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.unitsEquiv_apply, Units.val_oneSub,
        hgD]
      simp
    rw [e, hHcoe]
    exact (hdiff a).hasFDerivAt
  refine ⟨H.symm, fun x => H.apply_symm_apply x, fun y => H.symm_apply_apply y, hsymm, fun x => ?_⟩
  have hinvd : DifferentiableAt ℝ (H.symm : ℂ → ℂ) x := (hsymm.differentiable (by simp)) x
  have hcomp : (fderiv ℝ Ξ (H.symm x)).comp (fderiv ℝ (H.symm : ℂ → ℂ) x) =
      ContinuousLinearMap.id ℝ ℂ := by
    have h1 : Ξ ∘ (H.symm : ℂ → ℂ) = id := funext fun x => H.apply_symm_apply x
    have h2 := fderiv_comp x (hdiff (H.symm x)) hinvd
    rw [h1, fderiv_id] at h2
    exact h2.symm
  exact NIC.norm_sub_id_le_of_comp_eq_id hcomp (hD _) hε

/-! ## The packaged deterministic output -/

theorem IsNearIdDiffeo.mono {Φ Ψ : ℂ → ℂ} {U : Set ℂ} {ε ε' : ℝ} (h : IsNearIdDiffeo Φ Ψ U ε)
    (hεε' : ε ≤ ε') : IsNearIdDiffeo Φ Ψ U ε' :=
  ⟨h.contDiff, h.contDiff_inv, h.left_inv, h.right_inv, h.eq_id_off,
    fun z => (h.deriv_close z).trans hεε', h.holo_inv⟩

/-- **The deterministic output of the zoom (CC0 D6)** at one centre `z` and scale `r`, with constant
`C`: `Ξ` is a global `C^∞` near-identity diffeomorphism with inverse `Ξinv`, equal to the zoomed
inverse map `χ_{z,r} = zoomInv ϕ ψ z r` on `B̄_R` and to the identity off `B_{2R}`; `χ_{z,r}`
satisfies the Taylor bounds on `B̄_{2R}`. -/
structure IsZoomExt (ϕ ψ : ℂ → ℂ) (W : Set ℂ) (z : ℂ) (r R C : ℝ) (Ξ Ξinv : ℂ → ℂ) : Prop where
  /-- `(Ξ⁻¹, Ξ)` in the argument order of `NICInput` (`Φ = Ξ⁻¹`, `Ψ = Ξ`, `U = B_R`):
  `‖DΞ⁻¹ − I‖ ≤ C r`, and `Ξ` is holomorphic on `B_R` -/
  nearId : IsNearIdDiffeo Ξinv Ξ (ball 0 R) (C * r)
  /-- `‖DΞ − I‖ ≤ C r` -/
  fderiv_sub_le : ∀ y, ‖fderiv ℝ Ξ y - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * r
  /-- `Ξ = χ_{z,r}` on `B̄_R` -/
  eq_zoomInv : ∀ y ∈ closedBall (0 : ℂ) R, Ξ y = zoomInv ϕ ψ z r y
  /-- `Ξ = id` off `B_{2R}` -/
  eq_self : ∀ y : ℂ, 2 * R ≤ ‖y‖ → Ξ y = y
  /-- `Ξ⁻¹ = id` off `B_{2R}` -/
  inv_eq_self : ∀ x : ℂ, 2 * R ≤ ‖x‖ → Ξinv x = x
  /-- `|Ξ(y) − y| ≤ C r` -/
  norm_sub_le : ∀ y : ℂ, ‖Ξ y - y‖ ≤ C * r
  /-- `|Ξ⁻¹(x) − x| ≤ C r` -/
  inv_norm_sub_le : ∀ x : ℂ, ‖Ξinv x - x‖ ≤ C * r
  /-- `χ_{z,r}` is holomorphic on `B_{4R}` -/
  differentiableOn : DifferentiableOn ℂ (zoomInv ϕ ψ z r) (ball 0 (4 * R))
  /-- Taylor: `|χ(y) − y| ≤ C r |y|²` on `B̄_{2R}` -/
  taylor0 : ∀ y ∈ closedBall (0 : ℂ) (2 * R), ‖zoomInv ϕ ψ z r y - y‖ ≤ C * r * ‖y‖ ^ 2
  /-- Taylor: `|χ'(y) − 1| ≤ C r |y|` on `B̄_{2R}` -/
  taylor1 : ∀ y ∈ closedBall (0 : ℂ) (2 * R), ‖deriv (zoomInv ϕ ψ z r) y - 1‖ ≤ C * r * ‖y‖
  /-- Taylor: `|χ''(y)| ≤ C r` on `B̄_{2R}` -/
  taylor2 : ∀ y ∈ closedBall (0 : ℂ) (2 * R), ‖deriv (deriv (zoomInv ϕ ψ z r)) y‖ ≤ C * r
  /-- `ϕ'(z) ≠ 0` -/
  deriv_ne_zero : deriv ϕ z ≠ 0
  /-- link with the zoomed map `ϕ̃ = zoomMap ϕ z r` on `W̃ = zoomSet z r W`: `α_z χ(y) ∈ W̃` -/
  mem_zoomSet : ∀ y ∈ closedBall (0 : ℂ) (2 * R),
    (deriv ϕ z)⁻¹ * zoomInv ϕ ψ z r y ∈ zoomSet z r W
  /-- link with the zoomed map: `ϕ̃(α_z χ(y)) = y` -/
  zoomMap_eq : ∀ y ∈ closedBall (0 : ℂ) (2 * R),
    zoomMap ϕ z r ((deriv ϕ z)⁻¹ * zoomInv ϕ ψ z r y) = y

/-- `IsZoomExt` is monotone in the constant. -/
theorem IsZoomExt.mono {ϕ ψ : ℂ → ℂ} {W : Set ℂ} {z : ℂ} {r R C C' : ℝ} {Ξ Ξinv : ℂ → ℂ}
    (h : IsZoomExt ϕ ψ W z r R C Ξ Ξinv) (hCC' : C ≤ C') (hr : 0 ≤ r) :
    IsZoomExt ϕ ψ W z r R C' Ξ Ξinv := by
  have h1 : C * r ≤ C' * r := mul_le_mul_of_nonneg_right hCC' hr
  refine ⟨h.nearId.mono h1, fun y => (h.fderiv_sub_le y).trans h1, h.eq_zoomInv, h.eq_self,
    h.inv_eq_self, fun y => (h.norm_sub_le y).trans h1, fun x => (h.inv_norm_sub_le x).trans h1,
    h.differentiableOn, fun y hy => (h.taylor0 y hy).trans ?_,
    fun y hy => (h.taylor1 y hy).trans ?_, fun y hy => (h.taylor2 y hy).trans h1,
    h.deriv_ne_zero, h.mem_zoomSet, h.zoomMap_eq⟩
  · exact mul_le_mul_of_nonneg_right h1 (by positivity)
  · exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **Zoom and global extension, uniformly over a compact set (CC0 D6).** For `IsConfNbhd ϕ W V`
with left inverse `ψ`, a compact `Kc ⊆ V`, `R > 0` and a smallness level `η > 0`, there are
`r₁ > 0` and `C > 0` with `C r₁ ≤ η` such that for every `z ∈ Kc` and `r ∈ (0, r₁]` the extension
`Ξ = zoomExt ϕ ψ z r R` has an inverse `Ξinv` with `IsZoomExt ϕ ψ W z r R C Ξ Ξinv`. -/
theorem IsConfNbhd.exists_zoomExt {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V)
    (hψ : ∀ x ∈ W, ψ (ϕ x) = x) {Kc : Set ℂ} (hKc : IsCompact Kc) (hKcV : Kc ⊆ V)
    {R : ℝ} (hR : 0 < R) {η : ℝ} (hη : 0 < η) :
    ∃ r₁ C : ℝ, 0 < r₁ ∧ 0 < C ∧ C * r₁ ≤ η ∧ ∀ z ∈ Kc, ∀ r ∈ Ioc (0 : ℝ) r₁,
      ∃ Ξinv : ℂ → ℂ, IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv := by
  obtain ⟨δ, M₁, M₂, hδ, hM₁, hM₂, hball, hd1, hd2⟩ := hϕ.exists_zoom_consts hψ hKc hKcV
  obtain ⟨Mb, hMb0, hMb⟩ := exists_norm_fderiv_zoomCut_le
  have hKcW : Kc ⊆ W := hKcV.trans hϕ.subset
  set A : ℝ := M₁ * M₂ * (2 + 4 * Mb) * R with hAdef
  have hA0 : 0 ≤ A := by positivity
  set C : ℝ := 2 * A + 4 * M₁ * M₂ * R ^ 2 + M₁ * M₂ + 1 with hCdef
  have hC0 : 0 < C := by positivity
  have hAC : 2 * A ≤ C := by
    have : 0 ≤ 4 * M₁ * M₂ * R ^ 2 := by positivity
    have : 0 ≤ M₁ * M₂ := by positivity
    linarith
  have hBC : 4 * M₁ * M₂ * R ^ 2 ≤ C := by
    have : 0 ≤ M₁ * M₂ := by positivity
    linarith
  have hTC : M₁ * M₂ ≤ C := by
    have : 0 ≤ 4 * M₁ * M₂ * R ^ 2 := by positivity
    linarith
  set r₁ : ℝ := min (min (δ / (4 * R)) (1 / (2 * (A + 1)))) (η / C) with hr₁def
  have hr₁ : 0 < r₁ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hr₁δ : r₁ ≤ δ / (4 * R) := (min_le_left _ _).trans (min_le_left _ _)
  have hr₁A : r₁ ≤ 1 / (2 * (A + 1)) := (min_le_left _ _).trans (min_le_right _ _)
  have hr₁η : r₁ ≤ η / C := min_le_right _ _
  refine ⟨r₁, C, hr₁, hC0, ?_, fun z hz r hr => ?_⟩
  · calc C * r₁ ≤ C * (η / C) := mul_le_mul_of_nonneg_left hr₁η hC0.le
      _ = η := by field_simp
  obtain ⟨hr0, hrr₁⟩ := hr
  have hsmall : r * (4 * R) ≤ δ := by
    have := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * R)).1 (hrr₁.trans hr₁δ)
    linarith
  have H : ZoomHyp ϕ ψ W V z r R δ M₁ M₂ :=
    ⟨hϕ, hψ, hKcW hz, hball z hz, hd1 z hz, hd2 z hz, hM₁, hM₂, hr0, hR, hsmall⟩
  have hD := H.norm_fderiv_zoomExt_sub_le hMb0 (hMb R hR)
  have hAr : A * r ≤ 1 / 2 := by
    have h1 : r ≤ 1 / (2 * (A + 1)) := hrr₁.trans hr₁A
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hD' : ∀ y, ‖fderiv ℝ (zoomExt ϕ ψ z r R) y - ContinuousLinearMap.id ℝ ℂ‖ ≤ A * r :=
    fun y => (hD y).trans_eq (by rw [hAdef])
  obtain ⟨Ξinv, hl, hr', hcd, hDinv⟩ := exists_inverse_of_nearId H.contDiff_zoomExt hAr hD'
  have hinv_self : ∀ x : ℂ, 2 * R ≤ ‖x‖ → Ξinv x = x := fun x hx => by
    have := hr' x
    rwa [zoomExt_eq_self hR hx] at this
  have hrC : ∀ {a : ℝ}, a ≤ C → a * r ≤ C * r := fun h => mul_le_mul_of_nonneg_right h hr0.le
  refine ⟨Ξinv, ⟨⟨hcd, H.contDiff_zoomExt, hl, hr', ⟨2 * R, hinv_self⟩, fun x => ?_,
    H.differentiableOn_zoomExt⟩, fun y => (hD' y).trans (hrC (by linarith)),
    fun y hy => zoomExt_eq_zoomInv hR (mem_closedBall_zero_iff.1 hy),
    fun y hy => zoomExt_eq_self hR hy, hinv_self,
    fun y => (H.norm_zoomExt_sub_le y).trans (hrC hBC), fun x => ?_,
    H.differentiableOn, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    H.deriv_ne_zero, fun y hy => ?_, fun y hy => ?_⟩⟩
  · calc ‖fderiv ℝ Ξinv x - ContinuousLinearMap.id ℝ ℂ‖ ≤ 2 * (A * r) := hDinv x
      _ = (2 * A) * r := by ring
      _ ≤ C * r := hrC hAC
  · have e : Ξinv x - x = -(zoomExt ϕ ψ z r R (Ξinv x) - Ξinv x) := by
      rw [hl x]; ring
    rw [e, norm_neg]
    exact (H.norm_zoomExt_sub_le _).trans (hrC hBC)
  · have hy2 : ‖y‖ ≤ 4 * R := by linarith [mem_closedBall_zero_iff.1 hy]
    exact (H.norm_sub_le hy2).trans
      (mul_le_mul_of_nonneg_right (hrC hTC) (by positivity))
  · have hy2 : ‖y‖ ≤ 4 * R := by linarith [mem_closedBall_zero_iff.1 hy]
    exact (H.norm_deriv_sub_one_le hy2).trans
      (mul_le_mul_of_nonneg_right (hrC hTC) (norm_nonneg _))
  · have hy2 : ‖y‖ < 4 * R := by linarith [mem_closedBall_zero_iff.1 hy]
    exact (H.norm_deriv_deriv_le hy2).trans (hrC hTC)
  · exact H.mem_zoomSet (by linarith [mem_closedBall_zero_iff.1 hy])
  · exact H.zoomMap_eq (by linarith [mem_closedBall_zero_iff.1 hy])

end SmallGammaGeodesics.CC
