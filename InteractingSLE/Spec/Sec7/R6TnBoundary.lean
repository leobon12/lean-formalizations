/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FcCore
import InteractingSLE.Spec.Sec7.R6FcJordanInf

/-!
# Two-outer faces from agreement of the initial and current domains

PROVE-R6-TWO. The named geometric input `IsLandingPatch` concerns only
physical domains near one specified landing. The transition interval,
collars, real limits and complement agreement are conclusions, obtained
from the landed boundary correspondence and reflection theorems.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Tn

open PocketStopSide R6Safe R6Fc

/-- The one-chart boundary facts used below. All fields are supplied by
the Jordan and curve-generated Loewner theorems, in `R6TnChart`. -/
structure BoundaryChart (C P : Set ℂ) (O : Chart) (vL vR : ℝ) where
  coord : ℂ → ℂ
  hull : Set ℂ
  inverse : ℂ → ℂ
  conformal : O.IsConformal
  dom_eq : (O.dom : Set ℂ) = C ∩ coord ⁻¹' (H \ hull)
  inv_eq : EqOn inverse O.2.1 H
  inv_cont : ContinuousOn inverse Hbar
  inv_maps : MapsTo inverse Hbar P
  mem_boundary : C ⊆ P
  coord_mem : MapsTo coord C H
  coord_cont : ContinuousOn coord P
  classify : ∀ x : ℝ, coord (inverse x) ∈ closure hull ↔ x ∈ Icc vL vR
  detect : ∀ p ∈ P, ∀ r > 0,
    C ∩ ball p r ⊆ C ∩ coord ⁻¹' (H \ hull) → coord p ∉ closure hull
  norm_bound : ∃ B : ℝ, ∀ w ∈ (O.dom : Set ℂ), ‖O.1 w‖ ≤ ‖coord w‖ + B

namespace BoundaryChart

variable {C P : Set ℂ} {O : Chart} {vL vR : ℝ}

/-- The model's inverse equals the canonical extension at every real point. -/
theorem inverse_real (M : BoundaryChart C P O vL vR) (x : ℝ) :
    M.inverse x = extendFrom H O.2.1 (x : ℂ) := by
  apply Eq.symm
  exact extendFrom_eq (by rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact real_mem_Hbar x)
    (tendsto_of_extension M.inv_eq M.inv_cont x)

/-- The forward implication of boundary aliveness is just continuity of
the initial coordinate; the reverse implication is the landed Jordan theorem. -/
theorem alive_ball (M : BoundaryChart C P O vL vR) {p : ℂ} (hp : p ∈ P)
    (ha : M.coord p ∉ closure M.hull) :
    ∃ r > 0, C ∩ ball p r ⊆ C ∩ M.coord ⁻¹' (H \ M.hull) := by
  obtain ⟨r, hr, hrK⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ ha
  obtain ⟨s, hs, hsψ⟩ := Metric.continuousWithinAt_iff.1 (M.coord_cont p hp) r hr
  refine ⟨s, hs, fun w hw => ⟨hw.1, ?_, fun hwK => ?_⟩⟩
  · exact M.coord_mem hw.1
  · exact hrK (hsψ (M.mem_boundary hw.1) (mem_ball.1 hw.2)) (subset_closure hwK)

end BoundaryChart

/-- **Named geometric input.** At the canonical physical landing `p`,
the initial outer pocket locally lies in the inner pocket, and the
outer current domain locally lies in the inner current domain. `P` is
the inner pocket's closure with its outgoing pole removed (if finite).
No transition-chart or real-interval conclusion is assumed. -/
def IsLandingPatch (C V P : Set ℂ) (O I : Chart) (v : ℝ) : Prop :=
  let p := extendFrom H O.2.1 (v : ℂ)
  p ∈ P ∧ ∃ ε > 0, C ∩ ball p ε ⊆ V ∧ (O.dom : Set ℂ) ∩ ball p ε ⊆ I.dom

/-- R.6(b)--(d), shared side on the left, from physical local agreement
and the established one-chart boundary facts. -/
theorem r6FaceR_left_of_landingPatch {C V PC PV : Set ℂ} {O I : Chart}
    {ρL ρR σL σR vL vR wL wR : Fin 1 → ℝ}
    (MC : BoundaryChart C PC O (vL 0) (vR 0)) (MV : BoundaryChart V PV I (wL 0) (wR 0))
    (hVC : V ⊆ C) (hIncl : (I.dom : Set ℂ) ⊆ O.dom)
    (hvL : vL 0 < 0) (hvR : 0 < vR 0) (hwL : wL 0 < 0)
    (hρ : ρL 0 = σL 0) (hpatch : IsLandingPatch C V PV O I (vL 0)) :
    R6FaceR ρL ρR σL σR vL vR wL wR O I (H \ (O.dom : Set ℂ)) (H \ (I.dom : Set ℂ)) := by
  obtain ⟨hp, ε₀, hε₀, hinit, hcurrent⟩ := hpatch
  set p := extendFrom H O.2.1 (vL 0 : ℂ) with hpdef
  have hEp : MC.inverse (vL 0) = p := MC.inverse_real _
  obtain ⟨ε₁, hε₁, hε₁ψ⟩ := Metric.continuousWithinAt_iff.1 (MV.coord_cont p hp) 1 one_pos
  let ε : ℝ := min ε₀ ε₁
  have hε : 0 < ε := lt_min hε₀ hε₁
  have hinit' : C ∩ ball p ε ⊆ V := fun z hz => hinit ⟨hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩
  have hcurrent' : (O.dom : Set ℂ) ∩ ball p ε ⊆ I.dom :=
    fun z hz => hcurrent ⟨hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩
  obtain ⟨B, hB⟩ := MV.norm_bound
  have hbdd : ∀ w ∈ (I.dom : Set ℂ) ∩ ball (MC.inverse (vL 0)) ε,
      ‖I.1 w‖ ≤ ‖MV.coord p‖ + 1 + B := by
    intro w hw
    have hwV : w ∈ V := by rw [MV.dom_eq] at hw; exact hw.1.1
    have hwball : dist w p < ε₁ := by
      rw [hEp] at hw
      exact (mem_ball.1 hw.2).trans_le (min_le_right _ _)
    have hdist := hε₁ψ (MV.mem_boundary hwV) hwball
    have hn := norm_le_norm_add_norm_sub' (MV.coord w) (MV.coord p)
    rw [dist_eq_norm] at hdist
    have hb := hB w hw.1
    linarith
  have halive : ∀ z ∈ ball p (ε / 2), z ∈ PC → z ∈ PV →
      (MC.coord z ∉ closure MC.hull ↔ MV.coord z ∉ closure MV.hull) := by
    intro z hz hzC hzV
    apply alive_iff_of hVC
    · rw [← MC.dom_eq, ← MV.dom_eq]; exact hIncl
    · exact hinit'
    · rw [← MC.dom_eq, ← MV.dom_eq]; exact hcurrent'
    · exact hz
    · exact fun ha => MC.alive_ball hzC ha
    · exact fun r hr hsub => MC.detect z hzC r hr hsub
    · exact fun ha => MV.alive_ball hzV ha
    · exact fun r hr hsub => MV.detect z hzV r hr hsub
  obtain ⟨δ, hδ, hδE⟩ := Metric.continuousWithinAt_iff.1 (MC.inv_cont _ (real_mem_Hbar (vL 0)))
    (ε / 2) (half_pos hε)
  let d := min δ (vR 0 - vL 0)
  have hd : 0 < d := lt_min hδ (by linarith)
  have hnear : ∀ x : ℝ, |x - vL 0| < δ → MC.inverse x ∈ ball p (ε / 2) := by
    intro x hx
    rw [← hEp]
    apply hδE (real_mem_Hbar x)
    simpa only [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hx
  apply r6FaceR_left MC.conformal MV.conformal hIncl MC.inv_eq MC.inv_cont MV.inv_eq MV.inv_cont
    hvL hwL hρ hε (by rw [hEp]; exact hcurrent') hbdd hd
  · intro ξ hξ1 hξ2 x hx
    have hξ : ξ ∈ Icc (vL 0) (vR 0) := ⟨hξ1, by have := min_le_right δ (vR 0 - vL 0); dsimp [d] at hξ2; linarith⟩
    have hball := hnear ξ (by have := min_le_left δ (vR 0 - vL 0); dsimp [d] at hξ2; rw [abs_sub_lt_iff]; constructor <;> linarith)
    have hzV : MC.inverse ξ ∈ PV := hx ▸ MV.inv_maps (real_mem_Hbar x)
    have hi := halive _ hball (MC.inv_maps (real_mem_Hbar ξ)) hzV
    have hdead := (MC.classify ξ).2 hξ
    have hdeadV : MV.coord (MV.inverse x) ∈ closure MV.hull := by
      by_contra h
      have := hi.2 (by rwa [← hx])
      exact this hdead
    exact (MV.classify x).1 hdeadV
  · intro y hy1 hy2 x hx
    have hy : y ∉ Icc (vL 0) (vR 0) := fun h => (not_le_of_gt hy2) h.1
    have hball := hnear y (by have := min_le_left δ (vR 0 - vL 0); dsimp [d] at hy1; rw [abs_sub_lt_iff]; constructor <;> linarith)
    have hzV : MC.inverse y ∈ PV := hx ▸ MV.inv_maps (real_mem_Hbar x)
    have hi := halive _ hball (MC.inv_maps (real_mem_Hbar y)) hzV
    have hfree := hi.1 (fun h => hy ((MC.classify y).1 h))
    have hxI : x ∉ Icc (wL 0) (wR 0) := fun h => hfree (by rw [← hx]; exact (MV.classify x).2 h)
    simpa only [mem_Icc, not_and_or, not_le] using hxI

end InteractingSLE.Sec7.R6Tn
