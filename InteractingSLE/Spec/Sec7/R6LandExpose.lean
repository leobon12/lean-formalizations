/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6LandFactor

/-!
# R.6: exposed test points without singleton-access assumptions

PROVE-R6-LANDING; Astra's `r6_face_geometry`, Lemma 4.2 and Remark 6.4.
The existing no-constant-boundary-arc theorem supplies a landing distinct
from the tip on either prescribed side arbitrarily near the driver.
Combined with the singleton-current-tip collar, it gives the physical
local inclusion needed at the exposed test point. No condition is put
on the number of accesses at that exposed landing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Land

/-- A boundary landing distinct from the current tip can be chosen in
any one-sided interval at zero while remaining in a prescribed physical
open neighborhood of the tip. -/
theorem exists_exposed_landing {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H)
    (hc : ContinuousOn F Hbar) (hi : InjOn F H) {U : Set ℂ}
    (hU : IsOpen U) (h0 : F 0 ∈ U) {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hab : a < b) :
    ∃ x ∈ Ioo a b, F (x : ℂ) ∈ U ∧ F (x : ℂ) ≠ F 0 := by
  have hreal : Continuous fun x : ℝ => F (x : ℂ) :=
    hc.comp_continuous Complex.continuous_ofReal fun x => R6Fc.real_mem_Hbar x
  have hnhds : (fun x : ℝ => F (x : ℂ)) ⁻¹' U ∈ 𝓝 (0 : ℝ) :=
    hreal.continuousAt.preimage_mem_nhds (by simpa only [Complex.ofReal_zero] using hU.mem_nhds h0)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.1 hnhds
  have hlt : max a (-ε / 2) < min b (ε / 2) :=
    lt_min (max_lt hab (by linarith only [hb, hε]))
      (max_lt (by linarith only [ha, hε]) (by linarith only [hε]))
  obtain ⟨x, hx, hne⟩ := exists_ne_of_injOn hd hc hi hlt (F 0)
  refine ⟨x, ⟨(le_max_left _ _).trans_lt hx.1, hx.2.trans_le (min_le_left _ _)⟩, ?_, hne⟩
  apply hεU
  rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
  have hlo := (le_max_right a (-ε / 2)).trans_lt hx.1
  have hhi := hx.2.trans_le (min_le_right b (ε / 2))
  constructor <;> linarith only [hlo, hhi, hε]

/-- A driver collar with a singleton current tip supplies an exposed
landing with physical local inclusion on either required side. The
initial pocket neighborhood `U` can also avoid the certified frontiers. -/
theorem exists_exposed_landing_local {C P V U : Set ℂ} {O : Chart} {vL vR : ℝ}
    (M : R6Tn.BoundaryChart C P O vL vR) (hVO : V ⊆ (O.dom : Set ℂ))
    (hsingle : ∀ x : ℝ, M.inverse (x : ℂ) = M.inverse 0 → x = 0)
    {r : ℝ} (hr : 0 < r) (hcol : H ∩ ball (0 : ℂ) r ⊆ O.1 '' V)
    (hU : IsOpen U) (h0U : M.inverse 0 ∈ U) {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hab : a < b) :
    ∃ x ∈ Ioo a b, M.inverse (x : ℂ) ≠ M.inverse 0 ∧ M.inverse (x : ℂ) ∈ U ∧
      ∃ e > 0, (O.dom : Set ℂ) ∩ ball (M.inverse (x : ℂ)) e ⊆ V := by
  obtain ⟨ε, hε, hlocal⟩ := driver_collar_physical M hVO hsingle hr hcol
  have hd : DifferentiableOn ℂ M.inverse H := M.conformal.1.congr M.inv_eq
  have hi : InjOn M.inverse H := by
    intro z hz w hw heq
    apply M.conformal.injOn hz hw
    rwa [← M.inv_eq hz, ← M.inv_eq hw]
  obtain ⟨x, hx, hxU, hxne⟩ := exists_exposed_landing hd M.inv_cont hi
    (hU.inter isOpen_ball) ⟨h0U, mem_ball_self (half_pos hε)⟩ ha hb hab
  refine ⟨x, hx, hxne, hxU.1, ε / 2, half_pos hε, ?_⟩
  intro w hw
  apply hlocal
  refine ⟨hw.1, mem_ball.2 ?_⟩
  exact (dist_triangle w (M.inverse (x : ℂ)) (M.inverse 0)).trans_lt
    (by linarith only [mem_ball.1 hw.2, mem_ball.1 hxU.2])

/-- In the mixed case the contained-domain identity gives local
inclusion directly on the physical open pocket, without Aux. 136. -/
theorem exists_exposed_landing_local_of_open_inclusion
    {C P V U : Set ℂ} {O : Chart} {vL vR : ℝ}
    (M : R6Tn.BoundaryChart C P O vL vR)
    (hU : IsOpen U) (h0U : M.inverse 0 ∈ U)
    (hlocal : (O.dom : Set ℂ) ∩ U ⊆ V) {a b : ℝ}
    (ha : a ≤ 0) (hb : 0 ≤ b) (hab : a < b) :
    ∃ x ∈ Ioo a b, M.inverse (x : ℂ) ≠ M.inverse 0 ∧ M.inverse (x : ℂ) ∈ U ∧
      ∃ e > 0, (O.dom : Set ℂ) ∩ ball (M.inverse (x : ℂ)) e ⊆ V := by
  have hd : DifferentiableOn ℂ M.inverse H := M.conformal.1.congr M.inv_eq
  have hi : InjOn M.inverse H := by
    intro z hz w hw heq
    apply M.conformal.injOn hz hw
    rwa [← M.inv_eq hz, ← M.inv_eq hw]
  obtain ⟨x, hx, hxU, hxne⟩ := exists_exposed_landing hd M.inv_cont hi hU h0U ha hb hab
  obtain ⟨e, he, heU⟩ := Metric.mem_nhds_iff.1 (hU.mem_nhds hxU)
  exact ⟨x, hx, hxne, hxU, e, he, fun w hw => hlocal ⟨hw.1, heU hw.2⟩⟩

end InteractingSLE.Sec7.R6Land
