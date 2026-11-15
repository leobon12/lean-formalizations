/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInInstCharts
import InteractingSLE.Spec.Sec7.Aux119Reflect

/-!
# The inherited logarithm at a shared current side

PROVE-POCKET-SIDEIN. Reflection and an actual shared half-disc give a finite
complex limit of the existing derivative logarithm. The logarithm is never
renormalized: its integer is obtained by comparison on the upper half-disc.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open scoped Real
open QuantumZipper (H Hbar)
open QuantumZipper.CA (schwarzReflect)

namespace InteractingSLE.Sec7.PocketStopSide

/-- Reflection of an extension has the chart derivative at interior points. -/
theorem deriv_reflection_eq_chart {c : Chart} (hc : c.IsConformal)
    {G : ℂ → ℂ} (hExtensionEq : EqOn G c.1 c.dom) {z : ℂ}
    (hz : z ∈ c.dom) : deriv (schwarzReflect G) z = deriv c.1 z := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [c.dom.isOpen.mem_nhds hz] with w hw
  have hwH : w ∈ H := hc.dom_subset hw
  simp only [schwarzReflect, (show 0 ≤ w.im from hwH.le), ↓reduceIte]
  exact hExtensionEq hw

/-- An inherited analytic logarithm has a finite complex limit at the centre
of a reflected shared half-disc. Its exponential is the positive reflected
derivative, including the original integer branch. -/
theorem exists_tendsto_log_of_shared_halfDisc {c : Chart} (hc : c.IsConformal)
    {L G : ℂ → ℂ} (hL : IsDerivLog c.1 L c.dom)
    (hExtensionEq : EqOn G c.1 c.dom) {x r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hCollar : H ∩ ball (x : ℂ) r ⊆ (c.dom : Set ℂ))
    (hReflect : R16.IsRealBoundaryConformal G x s) :
    ∃ ℓ : ℂ, Tendsto L (𝓝[H] (x : ℂ)) (𝓝 ℓ) ∧
      exp ℓ = deriv (schwarzReflect G) x := by
  let Φ := deriv (schwarzReflect G)
  have hΦc : ContinuousOn Φ (ball (x : ℂ) s) :=
    (hReflect.differentiableOn_schwarzReflect.deriv isOpen_ball).continuousOn
  have hxb := mem_ball_self hs (x := (x : ℂ))
  obtain ⟨-, hΦpos⟩ := hReflect.deriv_schwarzReflect_pos hxb
  have hΦxc : ContinuousAt Φ (x : ℂ) := hΦc.continuousAt (ball_mem_nhds _ hs)
  obtain ⟨ε, hε, hεΦ⟩ := Metric.mem_nhds_iff.1
    (hΦxc.preimage_mem_nhds ((isOpen_lt continuous_const continuous_re).mem_nhds hΦpos))
  let ρ := min ε (min r s)
  have hρ : 0 < ρ := lt_min hε (lt_min hr hs)
  have hρr : ρ ≤ r := (min_le_right _ _).trans (min_le_left _ _)
  have hρs : ρ ≤ s := (min_le_right _ _).trans (min_le_right _ _)
  let S := ball (x : ℂ) ρ ∩ H
  have hSD : S ⊆ (c.dom : Set ℂ) := fun z hz =>
    hCollar ⟨hz.2, ball_subset_ball hρr hz.1⟩
  have hSconn : IsPreconnected S :=
    ((convex_ball (x : ℂ) ρ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hslit : ∀ z ∈ S, Φ z ∈ slitPlane := fun z hz =>
    Or.inl (hεΦ (ball_subset_ball (min_le_left _ _) hz.1))
  obtain ⟨n, hn⟩ := Aux119.exists_int_eqOn_sub (L₁ := fun _ => 0) (L₂ := L)
    hSconn continuousOn_const (hL.1.continuousOn.mono hSD)
    (hΦc.mono (fun _ hz => ball_subset_ball hρs hz.1)) hslit
    (fun z hz => by
      rw [sub_zero, hL.2 z (hSD hz)]
      exact (deriv_reflection_eq_chart hc hExtensionEq (hSD hz)).symm)
  let ℓ := log (Φ x) + n * (2 * π * I)
  have hlog : ContinuousAt (fun z => log (Φ z)) (x : ℂ) :=
    (continuousAt_clog (Or.inl hΦpos)).comp hΦxc
  have hlim : Tendsto L (𝓝[H] (x : ℂ)) (𝓝 ℓ) := by
    refine ((hlog.tendsto.mono_left nhdsWithin_le_nhds).add_const _).congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hρ)] with z hzH hzball
    have heq : L z = log (Φ z) + n * (2 * π * I) := by
      simpa only [sub_zero] using hn z ⟨hzball, hzH⟩
    exact heq.symm
  refine ⟨ℓ, hlim, ?_⟩
  have : NeBot (𝓝[H] (x : ℂ)) := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  apply tendsto_nhds_unique (Complex.continuous_exp.tendsto ℓ |>.comp hlim)
  refine (hΦxc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (ball_mem_nhds (x : ℂ) hr)] with z hzH hzball
  exact (hL.2 z (hCollar ⟨hzH, hzball⟩)).trans
    (deriv_reflection_eq_chart hc hExtensionEq (hCollar ⟨hzH, hzball⟩)).symm |>.symm

end InteractingSLE.Sec7.PocketStopSide
