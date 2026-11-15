/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrReflect

/-!
# The later reflected transition stays close to the same-time one

PROVE-R6-TWO, Astra §5. The estimate uses the exact shifted inverse
identity and the existing bounded-displacement estimate. It applies to
all surviving points, including their reflected real limits.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Tr

/-- Uniform smallness of a centered forward increment on its entire
surviving domain, with real elapsed times. -/
theorem uniform_forward_increment_small {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {q₀ : ℝ} (hq₀ : 0 ≤ q₀) {a : ℝ} (ha : 0 < a) :
    ∃ θ > 0, ∀ q : ℝ, q₀ < q → q < q₀ + θ → ∀ z ∈ H \ fwdHull W q,
      ‖fwdMap W q z - fwdMap W q₀ z‖ < a := by
  obtain ⟨r, hr, hrW⟩ := Metric.continuousAt_iff.1 hW.continuousAt (a / 48) (by positivity)
  let θ := min r ((a / 32) ^ 2)
  have hθ : 0 < θ := lt_min hr (by positivity)
  refine ⟨θ, hθ, fun q hlo hhi z hz => ?_⟩
  let u := q - q₀
  have hu : 0 ≤ u := sub_nonneg.2 hlo.le
  have huθ : u < θ := by dsimp [u]; linarith
  have hM : ∀ s ∈ Icc (0 : ℝ) u, |QuantumZipper.RS.shiftDrive W q₀ s| ≤ a / 48 := by
    intro s hs
    have hd : dist (q₀ + s) q₀ < r := by
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_nonneg hs.1]
      exact hs.2.trans_lt (huθ.trans_le (min_le_left _ _))
    exact (hrW hd).le
  let y := fwdMap W q z
  have hy : y ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW (hq₀.trans hlo.le) hz
  have hyinv : fwdMapInv W (q₀ + u) y = z := by
    rw [show q₀ + u = q by dsimp [u]; ring]
    exact QuantumZipper.RS.fwdMapInv_fwdMap hW hW0 (hq₀.trans hlo.le) hz
  have hshift : fwdMapInv (QuantumZipper.RS.shiftDrive W q₀) u y = fwdMap W q₀ z := by
    rw [QuantumZipper.RS.fwdMapInv_shift_eq hW hW0 hq₀ hu hy, hyinv]
  have hb := norm_fwdMapInv_sub_le (QuantumZipper.RS.continuous_shiftDrive hW q₀)
    (QuantumZipper.RS.shiftDrive_zero W q₀) hu hM hy
  rw [hshift, norm_sub_rev] at hb
  have hsqrt : Real.sqrt u < a / 32 := by
    rw [Real.sqrt_lt' (by positivity)]
    exact huθ.trans_le (min_le_right _ _)
  change ‖y - fwdMap W q₀ z‖ < a
  linarith

/-- A uniform bound for the physical forward increments passes to
any two reflected real transition limits, without identifying the
physical landing's other prime ends. -/
theorem reflected_limit_sub_le {O I₀ I₁ : Chart}
    (hO : O.IsConformal) (hI₀ : I₀.IsConformal) (hI₁ : I₁.IsConformal)
    (hi₀ : (I₀.dom : Set ℂ) ⊆ O.dom) (hi₁ : (I₁.dom : Set ℂ) ⊆ O.dom)
    (hsub : (I₁.dom : Set ℂ) ⊆ I₀.dom) {x : ℝ} {a b B : ℝ}
    (hcol : ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ ((PocketStopSide.pocketTransitionChart O I₁).dom : Set ℂ))
    (hlim₀ : Tendsto (PocketStopSide.pocketTransitionChart O I₀).1
      (𝓝[((PocketStopSide.pocketTransitionChart O I₀).dom : Set ℂ)] (x : ℂ)) (𝓝 (a : ℂ)))
    (hlim₁ : Tendsto (PocketStopSide.pocketTransitionChart O I₁).1
      (𝓝[((PocketStopSide.pocketTransitionChart O I₁).dom : Set ℂ)] (x : ℂ)) (𝓝 (b : ℂ)))
    (hB : ∀ w ∈ (I₁.dom : Set ℂ), ‖I₁.1 w - I₀.1 w‖ ≤ B) : |b - a| ≤ B := by
  have hTsub : ((PocketStopSide.pocketTransitionChart O I₁).dom : Set ℂ) ⊆
      (PocketStopSide.pocketTransitionChart O I₀).dom := by
    rw [PocketStopSide.dom_pocketTransitionChart hO hI₁ hi₁,
      PocketStopSide.dom_pocketTransitionChart hO hI₀ hi₀]
    exact image_mono hsub
  obtain ⟨r, hr, hcollar⟩ := hcol
  have hxcl : (x : ℂ) ∈ closure ((PocketStopSide.pocketTransitionChart O I₁).dom : Set ℂ) :=
    closure_mono hcollar (isOpen_ball.closure_inter ⟨by
      rw [closure_H]; exact R6Fc.real_mem_Hbar x, mem_ball_self hr⟩)
  have : (𝓝[((PocketStopSide.pocketTransitionChart O I₁).dom : Set ℂ)] (x : ℂ)).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.1 hxcl
  have hlim := (hlim₁.sub (hlim₀.mono_left (nhdsWithin_mono _ hTsub))).norm
  have hle : ‖(b : ℂ) - (a : ℂ)‖ ≤ B := le_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun z hz => hB (O.2.1 z)
      (((PocketStopSide.mem_dom_pocketTransitionChart hO hI₁ hi₁).1 hz).2))
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hle

end InteractingSLE.Sec7.R6Tr
