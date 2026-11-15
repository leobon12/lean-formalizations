/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrChain

/-!
# The common-time reflected transition on a connected incident interval

PROVE-R6-TWO, Astra §2.5 (R98). Collars and the ordinary one-chain
coordinate bound give finite real limits, positive reflection, and
strict increase on the whole shared interval, including the driver.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Sec7.R6Ts

open PocketStopSide R6Fc

/-- The local positive-reflection derivative gives strict increase on
any connected real interval. This extends the diameter version in
`R6FcCore` to the full incident interval. -/
theorem strictMonoOn_re_of_interval_reflection {G : ℂ → ℂ} {S : Set ℝ}
    (hS : IsPreconnected S)
    (hG : ∀ x ∈ S, ∃ r > 0, R16.IsRealBoundaryConformal G x r) :
    StrictMonoOn (fun x : ℝ => (G x).re) S := by
  have hd : ∀ x ∈ S, HasDerivAt (fun u : ℝ => (QuantumZipper.CA.schwarzReflect G u).re)
      (deriv (QuantumZipper.CA.schwarzReflect G) x).re x := by
    intro x hx
    obtain ⟨r, hr, hGr⟩ := hG x hx
    exact (hGr.differentiableOn_schwarzReflect.differentiableAt
      (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt.real_of_complex
  have hmono : StrictMonoOn (fun x : ℝ => (QuantumZipper.CA.schwarzReflect G x).re) S := by
    apply strictMonoOn_of_deriv_pos hS.convex
      (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    intro x hx
    have hxS : x ∈ S := interior_subset hx
    rw [(hd x hxS).deriv]
    obtain ⟨r, hr, hGr⟩ := hG x hxS
    exact (hGr.deriv_schwarzReflect_pos (mem_ball_self hr)).2
  simpa only [schwarzReflect_ofReal] using hmono

/-- Bounded inverse displacement and continuity of the initial inner
coordinate give local transition bounds at every shared landing.
The driver is permitted; no avoidance of the tip is required at the
common original time. -/
theorem transition_bound_of_innerChain
    {V P : Set ℂ} {I : ℝ → Chart} {p : ℂ} (M : R6Tr.InnerChain V P I p)
    {O : Chart} (hO : O.IsConformal)
    (hIncl : ((I M.time).dom : Set ℂ) ⊆ O.dom)
    {EO : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    {x : ℝ} (hxP : EO (x : ℂ) ∈ P) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝[((pocketTransitionChart O (I M.time)).dom : Set ℂ)] (x : ℂ),
      ‖(pocketTransitionChart O (I M.time)).1 z‖ ≤ B := by
  obtain ⟨B, hB⟩ := M.norm_bound M.time_mem
  obtain ⟨a, ha, haψ⟩ := Metric.continuousWithinAt_iff.1 (M.coord_cont _ hxP) 1 zero_lt_one
  obtain ⟨b, hb, hbE⟩ := Metric.continuousWithinAt_iff.1
    (hEOc _ (real_mem_Hbar x)) a ha
  refine ⟨‖M.coord (EO (x : ℂ))‖ + 1 + B, ?_⟩
  filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hb), self_mem_nhdsWithin]
    with z hzb hz
  have hw : O.2.1 z ∈ (I M.time).dom :=
    ((mem_dom_pocketTransitionChart hO (M.conformal M.time M.time_mem) hIncl).1 hz).2
  have hzH : z ∈ H :=
    (isConformal_pocketTransitionChart hO (M.conformal M.time M.time_mem) hIncl).dom_subset hz
  have hwV : O.2.1 z ∈ V := by
    have hw' : O.2.1 z ∈ ((I M.time).dom : Set ℂ) := hw
    rw [M.dom_eq M.time M.time_mem] at hw'
    exact hw'.1
  have he : dist (O.2.1 z) (EO (x : ℂ)) < a := by
    rw [← hEO hzH]
    exact hbE (QuantumZipper.H_subset_Hbar hzH) (mem_ball.1 hzb)
  have hψdist := haψ (M.mem_boundary hwV) he
  have hn := norm_le_norm_add_norm_sub' (M.coord (O.2.1 z)) (M.coord (EO (x : ℂ)))
  rw [dist_eq_norm] at hψdist
  have hbound := hB _ hw
  change ‖(I M.time).1 (O.2.1 z)‖ ≤ _
  linarith

/-- Construct the real, strictly increasing common-time transition
from incident collars. Only the geometric collars and landing
membership are inputs; boundedness and real limits are conclusions. -/
theorem real_transition_of_incident_collars
    {V P : Set ℂ} {I : ℝ → Chart} {p : ℂ} (M : R6Tr.InnerChain V P I p)
    {O : Chart} (hO : O.IsConformal)
    (hIncl : ((I M.time).dom : Set ℂ) ⊆ O.dom)
    {EO EI : ℂ → ℂ} (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hEI : EqOn EI (I M.time).2.1 H) (hEIc : ContinuousOn EI Hbar)
    {S : Set ℝ} (hSo : IsOpen S) (hSc : IsPreconnected S)
    (hcollars : ∀ x ∈ S, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆ O.1 '' ((I M.time).dom : Set ℂ))
    (hlanding : ∀ x ∈ S, EO (x : ℂ) ∈ P) :
    ∃ g : ℝ → ℝ, StrictMonoOn g S ∧ ContinuousOn g S ∧
      (∀ x ∈ S, EI (g x : ℂ) = EO (x : ℂ)) ∧
      (∀ x ∈ S, Tendsto (pocketTransitionChart O (I M.time)).1
        (𝓝[((pocketTransitionChart O (I M.time)).dom : Set ℂ)] (x : ℂ)) (𝓝 (g x : ℂ))) ∧
      (∀ x ∈ S, extendFrom ((pocketTransitionChart O (I M.time)).dom : Set ℂ)
        (pocketTransitionChart O (I M.time)).1 (x : ℂ) = (g x : ℂ)) := by
  have hI := M.conformal M.time M.time_mem
  have hTdom := dom_pocketTransitionChart hO hI hIncl
  have hc : ∀ x ∈ S, ∃ r > 0, H ∩ ball (x : ℂ) r ⊆
      ((pocketTransitionChart O (I M.time)).dom : Set ℂ) := by
    rw [hTdom]
    exact hcollars
  obtain ⟨G, hG, hGc, hGr, hGE⟩ := exists_transition_extension_of_inverse_and_bounds
    hO hI hIncl hEI hEIc hSo hc
    (fun x _ => tendsto_of_extension hEO hEOc x)
    (fun x hx => transition_bound_of_innerChain M hO hIncl hEO hEOc (hlanding x hx))
  let g : ℝ → ℝ := fun x => (G x).re
  have hGg : ∀ x ∈ S, G (x : ℂ) = (g x : ℂ) := by
    intro x hx
    obtain ⟨r, hr, hGrx⟩ := hGr x hx
    exact Complex.ext rfl (hGrx.2.2.1 x (mem_ball_self hr) (Complex.ofReal_im x))
  have hlim : ∀ x ∈ S, Tendsto (pocketTransitionChart O (I M.time)).1
      (𝓝[((pocketTransitionChart O (I M.time)).dom : Set ℂ)] (x : ℂ)) (𝓝 (g x : ℂ)) := by
    intro x hx
    have h := ((hGc _ (Or.inr ⟨x, hx, rfl⟩)).mono subset_union_left).tendsto
    rw [hGg x hx] at h
    exact h.congr' (eventually_nhdsWithin_of_forall fun z hz => hG hz)
  refine ⟨g, strictMonoOn_re_of_interval_reflection hSc hGr,
    Complex.continuous_re.comp_continuousOn (hGc.comp Complex.continuous_ofReal.continuousOn
      (fun x hx => Or.inr ⟨x, hx, rfl⟩)), ?_, hlim, ?_⟩
  · intro x hx
    rw [← hGg x hx]
    exact hGE x hx
  · intro x hx
    obtain ⟨r, hr, hrc⟩ := hc x hx
    have hxH : (x : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
      exact real_mem_Hbar x
    have hxcl := closure_mono hrc (isOpen_ball.closure_inter ⟨hxH, mem_ball_self hr⟩)
    exact extendFrom_eq hxcl (hlim x hx)

end InteractingSLE.Sec7.R6Ts
