import SmallGammaGeodesics.CC.Lemma23Zoom
import SmallGammaGeodesics.CC.Prop21Det
import GaussianLQG.LQG.Bridge.Affine

/-!
# [3] Prop 2.1: the near-identity coupling as a conformal coupling of the zoomed map
(packet CC6b; CC0 Details D10)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D10**: "choose the fresh
GFF `g := ĝ(α_z⁻¹ ·)` on the NIC space of `χ_{z,r}` … since `g ∘ ψ̃ = ĝ ∘ χ` and
`ϕ̃ = χ⁻¹(α_z⁻¹ ·)` …". We make this a deterministic statement about one sample.

Notation: `ϕ̃ = zoomMap ϕ z r` on `W̃ = zoomSet z r W`, `c = ϕ'(z)` (`α_z = c⁻¹`),
`χ = zoomInv ϕ ψ z r`, the inverse zoom `ψ̃ = c⁻¹ χ` (`zoomPsi`), the global near-identity extension
`Ξ = zoomExt ϕ ψ z r R` of `χ` with inverse `Ξinv` (`IsZoomExt`), `B = B_{R/2}`, and the local
domain `Ṽ_B = ψ̃(B)` with `ϕ̃(Ṽ_B) = B`.

* `zoomPsi_zoomMap`: `ψ̃` is a left inverse of `ϕ̃` on `W̃`; `zoomMap_zoomPsi`, `zoomPsi_mem`;
* the derivative identities on `B`: `norm_deriv_zoomMap_zoomPsi_mul` (`|ϕ̃'(ψ̃ y)| |Ξ'(y)| = |c|`),
  `abs_det_fderiv_inv_mul` (`|det DΞinv(Ξ y)| |Ξ'(y)|² = 1`), `deriv_zoomPsi`
  (`ψ̃'(y) = c⁻¹ Ξ'(y)`);
* `zoomDom c x = x(c ·)` (`rotDist (c/|c|) (affineComp |c| 0 x)`), and its pairing
  `zoomDom_apply_eq`: `⟨x(c ·), τ⟩ = ⟨x, |c|⁻² τ(c⁻¹ ·)⟩`;
* `zoomTest_eq` (**the pullback identity**): for `g` supported in `B` with `ϕ̃`-pullback `τg`,
  `|c|⁻² τg(c⁻¹ x) = |det DΞinv(x)| g(Ξinv x)` for every `x`, i.e. the conformal pullback by the
  zoomed map followed by the rotation-dilation is the NIC transport by `Ξinv`;
* **`isConfCoupling_of_nic`**: if `(h, h̄, K)` satisfies the NIC identity of `Ξinv` on `B_R`, then
  `(h(c ·), h̄, f')` is a conformal coupling of `(ϕ̃, W̃, Ṽ_B)` for any continuous
  `f' = K + Q log|ψ̃'|` on `B` (D10's `f' = K + Q log|α_z| + Q log|χ'|`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- **The inverse zoom** `ψ̃(y) = ϕ'(z)⁻¹ χ_{z,r}(y) = r⁻¹(ψ(ϕ(z) + r y) − z)`. -/
def zoomPsi (ϕ ψ : ℂ → ℂ) (z : ℂ) (r : ℝ) (y : ℂ) : ℂ :=
  (deriv ϕ z)⁻¹ * zoomInv ϕ ψ z r y

/-- **The rotated and dilated field** `x(c ·) = (x(|c| ·))((c/|c|) ·)`. -/
def zoomDom (c : ℂ) (x : DistC) : DistC :=
  GaussianLQG.rotDist (c / (‖c‖ : ℂ)) (affineComp ‖c‖ 0 x)

section Geometry

variable {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} {z : ℂ} {r R C : ℝ} {Ξinv : ℂ → ℂ}

theorem zoomPsi_eq (hc : deriv ϕ z ≠ 0) (y : ℂ) :
    zoomPsi ϕ ψ z r y = (ψ (ϕ z + r * y) - z) / r := by
  rw [zoomPsi, zoomInv_def, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- `z + r ψ̃(y) = ψ(ϕ(z) + r y)` -/
theorem zoomAff_zoomPsi (hr : 0 < r) (hc : deriv ϕ z ≠ 0) (y : ℂ) :
    z + (r : ℂ) * zoomPsi ϕ ψ z r y = ψ (ϕ z + r * y) := by
  rw [zoomPsi_eq hc, zoomAff_div hr.ne']

/-- `ψ̃` is a left inverse of `ϕ̃` on `W̃`. -/
theorem zoomPsi_zoomMap (hr : 0 < r) (hc : deriv ϕ z ≠ 0) (hψ : ∀ x ∈ W, ψ (ϕ x) = x)
    {w : ℂ} (hw : w ∈ zoomSet z r W) : zoomPsi ϕ ψ z r (zoomMap ϕ z r w) = w := by
  rw [zoomPsi_eq hc, zoomAff_zoomMap hr.ne', hψ _ hw, div_zoomAff hr.ne']

theorem zoomPsi_mem (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv) {y : ℂ}
    (hy : y ∈ closedBall (0 : ℂ) (2 * R)) : zoomPsi ϕ ψ z r y ∈ zoomSet z r W :=
  hZ.mem_zoomSet y hy

theorem zoomMap_zoomPsi (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv) {y : ℂ}
    (hy : y ∈ closedBall (0 : ℂ) (2 * R)) : zoomMap ϕ z r (zoomPsi ϕ ψ z r y) = y :=
  hZ.zoomMap_eq y hy

/-- `Ξ = χ` near every point of `B_R` -/
theorem zoomExt_eventuallyEq (hR : 0 < R) {y : ℂ} (hy : y ∈ ball (0 : ℂ) R) :
    zoomExt ϕ ψ z r R =ᶠ[𝓝 y] zoomInv ϕ ψ z r :=
  Filter.eventually_of_mem (isOpen_ball.mem_nhds hy) fun _ hw =>
    zoomExt_eq_zoomInv hR (le_of_lt (mem_ball_zero_iff.1 hw))

/-- `ψ̃'(y) = c⁻¹ Ξ'(y)` on `B_R` -/
theorem deriv_zoomPsi (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv) (hR : 0 < R)
    {y : ℂ} (hy : y ∈ ball (0 : ℂ) R) :
    deriv (zoomPsi ϕ ψ z r) y = (deriv ϕ z)⁻¹ * deriv (zoomExt ϕ ψ z r R) y := by
  have hy4 : y ∈ ball (0 : ℂ) (4 * R) := ball_subset_ball (by linarith) hy
  have hdiff : DifferentiableAt ℂ (zoomInv ϕ ψ z r) y :=
    hZ.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hy4)
  rw [(zoomExt_eventuallyEq (ϕ := ϕ) (ψ := ψ) (z := z) (r := r) hR hy).deriv_eq]
  show deriv (fun y => (deriv ϕ z)⁻¹ * zoomInv ϕ ψ z r y) y = _
  exact deriv_const_mul _ hdiff

/-- `Ξ` is complex differentiable on `B_R`. -/
theorem differentiableAt_zoomExt (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv)
    {y : ℂ} (hy : y ∈ ball (0 : ℂ) R) : DifferentiableAt ℂ (zoomExt ϕ ψ z r R) y :=
  hZ.nearId.holo_inv.differentiableAt (isOpen_ball.mem_nhds hy)

/-- `ϕ(z) + r y ∈ ϕ(W)` for `y ∈ B̄_{2R}`. -/
theorem zoomAff_mem_image (hr : 0 < r) (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv)
    {y : ℂ} (hy : y ∈ closedBall (0 : ℂ) (2 * R)) : ϕ z + (r : ℂ) * y ∈ ϕ '' W := by
  have hm := zoomPsi_mem hZ hy
  have he := zoomMap_zoomPsi hZ hy
  rw [mem_zoomSet, zoomAff_zoomPsi hr hZ.deriv_ne_zero] at hm
  refine ⟨ψ (ϕ z + r * y), hm, ?_⟩
  have := zoomAff_zoomMap (ϕ := ϕ) (z := z) hr.ne' (zoomPsi ϕ ψ z r y)
  rw [he, zoomAff_zoomPsi hr hZ.deriv_ne_zero] at this
  exact this.symm

/-- **`|ϕ̃'(ψ̃ y)| |Ξ'(y)| = |c|`** on `B_R`. -/
theorem norm_deriv_zoomMap_zoomPsi_mul (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ x ∈ W, ψ (ϕ x) = x)
    (hr : 0 < r) (hR : 0 < R) (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv) {y : ℂ}
    (hy : y ∈ ball (0 : ℂ) R) :
    ‖deriv (zoomMap ϕ z r) (zoomPsi ϕ ψ z r y)‖ * ‖deriv (zoomExt ϕ ψ z r R) y‖ =
      ‖deriv ϕ z‖ := by
  have hy2 : y ∈ closedBall (0 : ℂ) (2 * R) :=
    mem_closedBall_zero_iff.2 (by linarith [mem_ball_zero_iff.1 hy])
  have hc := hZ.deriv_ne_zero
  have hm := zoomPsi_mem hZ hy2
  have hp := zoomAff_mem_image hr hZ hy2
  rw [mem_zoomSet] at hm
  have hd : DifferentiableAt ℂ ϕ (z + r * zoomPsi ϕ ψ z r y) :=
    hϕ.differentiableOn.differentiableAt (hϕ.isOpen_W.mem_nhds hm)
  rw [deriv_zoomMap hr.ne' hd, (zoomExt_eventuallyEq hR hy).deriv_eq,
    (hasDerivAt_zoomInv hϕ hψ hr hp).deriv, zoomAff_zoomPsi hr hc, ← norm_mul]
  congr 1
  have h1 := deriv_mul_deriv_leftInv hϕ.isOpen_W hϕ.differentiableOn hϕ.injOn hψ hp
  calc deriv ϕ (ψ (ϕ z + r * y)) * (deriv ϕ z * deriv ψ (ϕ z + r * y))
      = deriv ϕ z * (deriv ϕ (ψ (ϕ z + r * y)) * deriv ψ (ϕ z + r * y)) := by ring
    _ = deriv ϕ z := by rw [h1, mul_one]

/-- `det DΞ ∈ [1 − 2 C r, 1 + 2 C r + 2 (C r)²]` (near identity). -/
theorem det_fderiv_zoomExt_bounds (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv)
    (hCr : C * r ≤ 1) (y : ℂ) :
    1 - 2 * (C * r) ≤ (fderiv ℝ (zoomExt ϕ ψ z r R) y).det ∧
      (fderiv ℝ (zoomExt ϕ ψ z r R) y).det ≤ 1 + 2 * (C * r) + 2 * (C * r) ^ 2 :=
  NIC.det_bounds (hZ.fderiv_sub_le y) hCr

/-- `|det DΞ(y)| = |Ξ'(y)|²` on `B_R`. -/
theorem abs_det_fderiv_zoomExt (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv) {y : ℂ}
    (hy : y ∈ ball (0 : ℂ) R) :
    |(fderiv ℝ (zoomExt ϕ ψ z r R) y).det| = ‖deriv (zoomExt ϕ ψ z r R) y‖ ^ 2 :=
  QuantumZipper.abs_det_fderiv_eq_normSq (differentiableAt_zoomExt hZ hy)

/-- `Ξ'(y) ≠ 0` on `B_R` when `C r < 1/2`. -/
theorem deriv_zoomExt_ne_zero (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv)
    (hCr : C * r < 1 / 2) {y : ℂ} (hy : y ∈ ball (0 : ℂ) R) :
    deriv (zoomExt ϕ ψ z r R) y ≠ 0 := by
  intro h0
  have h1 := abs_det_fderiv_zoomExt hZ hy
  rw [h0, norm_zero] at h1
  have h2 := (det_fderiv_zoomExt_bounds hZ (by linarith) y).1
  have h3 : (fderiv ℝ (zoomExt ϕ ψ z r R) y).det = 0 := by
    have := abs_eq_zero.1 (h1.trans (by norm_num))
    exact this
  linarith

/-- **`|det DΞinv(Ξ y)| |det DΞ(y)| = 1`** (chain rule for `Ξinv ∘ Ξ = id`). -/
theorem abs_det_fderiv_inv_mul (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv)
    (y : ℂ) :
    |(fderiv ℝ Ξinv (zoomExt ϕ ψ z r R y)).det| * |(fderiv ℝ (zoomExt ϕ ψ z r R) y).det| = 1 := by
  have hN := hZ.nearId
  have hd1 : DifferentiableAt ℝ Ξinv (zoomExt ϕ ψ z r R y) :=
    (hN.contDiff.differentiable (by simp)) _
  have hd2 : DifferentiableAt ℝ (zoomExt ϕ ψ z r R) y :=
    (hN.contDiff_inv.differentiable (by simp)) _
  have hcomp : (fderiv ℝ Ξinv (zoomExt ϕ ψ z r R y)).comp (fderiv ℝ (zoomExt ϕ ψ z r R) y) =
      ContinuousLinearMap.id ℝ ℂ := by
    have h1 : Ξinv ∘ zoomExt ϕ ψ z r R = id := funext fun x => hN.right_inv x
    have h2 := fderiv_comp y hd1 hd2
    rw [h1, fderiv_id] at h2
    exact h2.symm
  rw [← abs_mul, ← NIC.det_comp, hcomp, NIC.det_id, abs_one]

end Geometry

/-! ## The rotated and dilated field -/

section Dom

/-- the test function `|c|⁻² τ(c⁻¹ ·)` -/
def zoomTest (c : ℂ) (τ : TestC) : TestC :=
  (‖c‖ ^ 2)⁻¹ • testAffinePull ‖c‖ 0 (GaussianLQG.testRot (c / (‖c‖ : ℂ)) τ)

theorem zoomTest_apply {c : ℂ} (hc : c ≠ 0) (τ : TestC) (x : ℂ) :
    zoomTest c τ x = (‖c‖ ^ 2)⁻¹ * τ (c⁻¹ * x) := by
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have hn' : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn
  have hb : c / (‖c‖ : ℂ) ≠ 0 := div_ne_zero hc hn'
  rw [zoomTest, smul_apply, testAffinePull_apply _ _ hn, GaussianLQG.testRot_apply hb, sub_zero]
  congr 2
  field_simp

/-- `⟨x(c ·), τ⟩ = ⟨x, |c|⁻² τ(c⁻¹ ·)⟩` -/
theorem zoomDom_apply_eq (c : ℂ) (x : DistC) (τ : TestC) :
    zoomDom c x τ = x (zoomTest c τ) := by
  rw [zoomDom, GaussianLQG.rotDist_apply, GFFInv.affineComp_apply, zoomTest, map_smul,
    smul_eq_mul]

end Dom

/-! ## The pullback identity -/

section Pullback

variable {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} {z : ℂ} {r R C : ℝ} {Ξinv : ℂ → ℂ}

/-- **The pullback identity**: for `g` supported in `B = B_{R/2}` with `ϕ̃`-pullback `τg` on `W̃`,
`|c|⁻² τg(c⁻¹ x) = |det DΞinv(x)| g(Ξinv x)` for every `x`. -/
theorem zoomTest_eq (hϕ : IsConfNbhd ϕ W V) (hψ : ∀ x ∈ W, ψ (ϕ x) = x) (hr : 0 < r)
    (hR : 0 < R) (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv) (hCr : C * r < 1 / 2)
    {g τg : TestC} (hg : tsupport (g : ℂ → ℝ) ⊆ ball 0 (R / 2))
    (hτ : IsConfPull (zoomMap ϕ z r) (zoomSet z r W) g τg) (x : ℂ) :
    zoomTest (deriv ϕ z) τg x = |(fderiv ℝ Ξinv x).det| * g (Ξinv x) := by
  have hc := hZ.deriv_ne_zero
  have hB : ball (0 : ℂ) (R / 2) ⊆ ball 0 R := ball_subset_ball (by linarith)
  have hB2 : ball (0 : ℂ) (R / 2) ⊆ closedBall 0 (2 * R) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hBR : ∀ y ∈ ball (0 : ℂ) (R / 2), y ∈ closedBall (0 : ℂ) R := fun y hy =>
    ball_subset_closedBall (hB hy)
  rw [zoomTest_apply hc, hτ ((deriv ϕ z)⁻¹ * x)]
  by_cases hgx : g (Ξinv x) = 0
  · -- the transport vanishes; so does the pullback
    rw [hgx, mul_zero, mul_eq_zero]
    right
    by_cases hW : (deriv ϕ z)⁻¹ * x ∈ zoomSet z r W
    · rw [indicator_of_mem hW, mul_eq_zero]
      right
      by_contra hne
      have hy : zoomMap ϕ z r ((deriv ϕ z)⁻¹ * x) ∈ ball (0 : ℂ) (R / 2) :=
        hg (subset_tsupport _ hne)
      set y := zoomMap ϕ z r ((deriv ϕ z)⁻¹ * x) with hydef
      have h1 : zoomPsi ϕ ψ z r y = (deriv ϕ z)⁻¹ * x := by
        rw [hydef, zoomPsi_zoomMap hr hc hψ hW]
      have h2 : x = zoomExt ϕ ψ z r R y := by
        rw [zoomExt_eq_zoomInv hR (mem_closedBall_zero_iff.1 (hBR y hy))]
        have := congrArg (fun w => deriv ϕ z * w) h1
        simp only [zoomPsi] at this
        rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul, ← mul_assoc, mul_inv_cancel₀ hc,
          one_mul] at this
        exact this.symm
      have h3 : Ξinv x = y := by rw [h2]; exact hZ.nearId.right_inv y
      rw [h3] at hgx
      exact hne hgx
    · rw [indicator_of_notMem hW]
  · -- the transport point lies in `B`
    have hy : Ξinv x ∈ ball (0 : ℂ) (R / 2) := hg (subset_tsupport _ hgx)
    set y := Ξinv x with hydef
    have hxy : zoomExt ϕ ψ z r R y = x := hZ.nearId.left_inv x
    have hχ : zoomInv ϕ ψ z r y = x := by
      rw [← hxy, zoomExt_eq_zoomInv hR (mem_closedBall_zero_iff.1 (hBR y hy))]
    have hpsi : zoomPsi ϕ ψ z r y = (deriv ϕ z)⁻¹ * x := by rw [zoomPsi, hχ]
    have hW : (deriv ϕ z)⁻¹ * x ∈ zoomSet z r W := hpsi ▸ zoomPsi_mem hZ (hB2 hy)
    have hmap : zoomMap ϕ z r ((deriv ϕ z)⁻¹ * x) = y := hpsi ▸ zoomMap_zoomPsi hZ (hB2 hy)
    rw [indicator_of_mem hW, hmap, ← mul_assoc]
    congr 1
    -- `|c|⁻² |ϕ̃'(ψ̃ y)|² = |det DΞinv(x)|`
    have hd2 := norm_deriv_zoomMap_zoomPsi_mul hϕ hψ hr hR hZ (hB hy)
    have hd1 := abs_det_fderiv_inv_mul hZ y
    rw [hxy, abs_det_fderiv_zoomExt hZ (hB hy)] at hd1
    rw [hpsi] at hd2
    have hne := deriv_zoomExt_ne_zero hZ hCr (hB hy)
    have hn0 : ‖deriv (zoomExt ϕ ψ z r R) y‖ ≠ 0 := norm_ne_zero_iff.2 hne
    have hc0 : ‖deriv ϕ z‖ ≠ 0 := norm_ne_zero_iff.2 hc
    have e1 : ‖deriv (zoomMap ϕ z r) ((deriv ϕ z)⁻¹ * x)‖ =
        ‖deriv ϕ z‖ / ‖deriv (zoomExt ϕ ψ z r R) y‖ := by
      rw [eq_div_iff hn0, hd2]
    have e2 : |(fderiv ℝ Ξinv x).det| = 1 / ‖deriv (zoomExt ϕ ψ z r R) y‖ ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hn0), hd1]
    rw [e1, e2]
    field_simp

/-- **The NIC coupling as a conformal coupling of the zoomed map** (D10). Let `(h, h̄, K)` satisfy
the NIC identity of `Ξinv` on `B_R` (one sample of `IsNICCoupling.coupling`), let `K̃` be continuous
with `K̃ = K` on `B = B_{R/2}`, and let `f'` be continuous with `f' = K + Q log|ψ̃'|` on `B`. If
`ψ̃(B) ⊆ Ṽ`, then `(h(c ·), h̄, f')` is a conformal coupling of `(ϕ̃, W̃, ψ̃(B))`. -/
theorem isConfCoupling_of_nic {γ : ℝ} (hγ : 0 < γ) (hϕ : IsConfNbhd ϕ W V)
    (hψ : ∀ x ∈ W, ψ (ϕ x) = x)
    (hr : 0 < r) (hR : 0 < R) (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv)
    (hCr : C * r < 1 / 2) (hVt : zoomPsi ϕ ψ z r '' ball 0 (R / 2) ⊆ zoomSet z r V)
    {hN hbN : DistC} {K : ℂ → ℝ}
    (hcoup : ∀ g τg : TestC, tsupport (g : ℂ → ℝ) ⊆ ball 0 R →
      (∀ x, τg x = |LinearMap.det (fderiv ℝ Ξinv x : ℂ →ₗ[ℝ] ℂ)| * g (Ξinv x)) →
      hN τg = hbN g + ∫ y, K y * g y)
    {Kt f' : C(ℂ, ℝ)} (hKt : ∀ y ∈ ball (0 : ℂ) (R / 2), Kt y = K y)
    (hf' : ∀ y ∈ ball (0 : ℂ) (R / 2),
      f' y = K y + Q γ * Real.log ‖deriv (zoomPsi ϕ ψ z r) y‖) :
    IsConfCoupling γ (zoomMap ϕ z r) (zoomSet z r W) (zoomPsi ϕ ψ z r '' ball 0 (R / 2))
      (zoomDom (deriv ϕ z) hN) hbN f' := by
  have hc := hZ.deriv_ne_zero
  have hB : ball (0 : ℂ) (R / 2) ⊆ ball 0 R := ball_subset_ball (by linarith)
  have hB2 : ball (0 : ℂ) (R / 2) ⊆ closedBall 0 (2 * R) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  -- the zoomed conformal neighbourhood on the local domain
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
    refine (image_congr fun y hy => zoomMap_zoomPsi hZ (hB2 hy)).trans (image_id _)
  intro g τg hg hτ
  rw [himg] at hg
  -- the pairing: NIC identity
  have hpair : zoomDom (deriv ϕ z) hN τg = hbN g + ∫ y, K y * g y := by
    rw [zoomDom_apply_eq]
    exact hcoup g _ (hg.trans hB) fun x => zoomTest_eq hϕ hψ hr hR hZ hCr hg hτ x
  -- the Liouville term
  have hlog := hτ.integral_log_mul hϕt (fun w hw => zoomPsi_zoomMap hr hc hψ hw)
    (by rw [himg]; exact hg)
  rw [hpair, hlog]
  -- pointwise identities on the support of `g`
  have hgK : ∀ y, K y * g y = Kt y * g y := fun y => by
    by_cases hgy : g y = 0
    · rw [hgy, mul_zero, mul_zero]
    · rw [hKt y (hg (subset_tsupport _ hgy))]
  have hQ : Q γ ≠ 0 := (Q_pos hγ).ne'
  have hgL : ∀ y, Real.log ‖deriv (zoomPsi ϕ ψ z r) y‖ * g y =
      (Q γ)⁻¹ * ((f' y - Kt y) * g y) := fun y => by
    by_cases hgy : g y = 0
    · rw [hgy, mul_zero, mul_zero, mul_zero]
    · have hyB := hg (subset_tsupport _ hgy)
      rw [hf' y hyB, hKt y hyB]
      field_simp
      ring
  have hint1 : Integrable (fun y => Kt y * g y) :=
    (Kt.continuous.mul g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
  have hint2 : Integrable (fun y => f' y * g y) :=
    (f'.continuous.mul g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
  simp_rw [hgK, hgL]
  rw [integral_const_mul]
  have e : (fun y => (f' y - Kt y) * g y) = fun y => f' y * g y - Kt y * g y := by
    funext y; ring
  rw [e, integral_sub hint2 hint1]
  field_simp
  ring

end Pullback

end SmallGammaGeodesics.CC
