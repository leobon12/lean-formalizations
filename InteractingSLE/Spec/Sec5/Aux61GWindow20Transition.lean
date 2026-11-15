/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWindow20Collar

/-! # The counterflow transition at a common access

The physical access identifies which real boundary value of the reflected
transition corresponds to the chart landing. Multiple prime ends at the
physical point require no additional assumption.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61GWindow20
open WangWu Aux61Cmp Aux61Restart Aux61TwoS

/-- A common physical access fixes the boundary value of the reflected
transition, hence its inverse has the actual counterflow landing limit. -/
theorem tendsto_transition_of_common_access {w : ℝ → ℝ} {γ η : ℝ → ℂ} {s r x y : ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsLoewnerTrace w γ) (hs : 0 ≤ s)
    {c : Chart} (hc : c.IsConformal)
    (hsub : (c.dom : Set ℂ) ⊆ H \ negInv '' fwdHull w s)
    (hB : IsHPHull (stripTargetHull (c.dom : Set ℂ))) {a ξ : ℝ}
    (hscale : EqOn c.1 (fun z => (a : ℂ) *
      (ConformalImage.mapOut (stripTargetHull (c.dom : Set ℂ)) (stripRightRetarget z) - ξ)) c.dom)
    {b : ℂ} (hdom : (c.dom : Set ℂ) = restartComponent (negInv '' fwdHull w s) η r b)
    (hclosed : IsClosed (η '' Icc 0 r)) (hx : x ≠ 0)
    (hH : cfBdry w s x ∈ H) (hpre : cfBdry w s x ∉ η '' Icc 0 r)
    (hone : cfBdry w s x ≠ 1)
    {A : Type*} {l : Filter A} [l.NeBot] {ρ : A → ℂ}
    (hinside : ∀ᶠ v in l, ρ v ∈ c.dom)
    (hcf : Tendsto (fun v => revChart w s (ρ v)) l (𝓝[H] (x : ℂ)))
    (hchart : Tendsto (fun v => c.1 (ρ v)) l (𝓝 (y : ℂ))) :
    Tendsto (fun z => revChart w s (c.2.1 z)) (𝓝[H] (y : ℂ)) (𝓝[H] (x : ℂ)) := by
  have hfreq : ∃ᶠ z in 𝓝[H] (x : ℂ), revChartInv w s z ∈ (c.dom : Set ℂ) := by
    apply hcf.frequently
    exact (hinside.mono fun v hv => by rw [revChartInv_revChart hw hw0 hs (hsub hv)]; exact hv).frequently
  obtain ⟨δ, hδ, hcol, hfin⟩ := exists_cfCollar_of_frequent hw hw0 hγ hs hdom hclosed hx hH hpre hone hfreq
  obtain ⟨G, hG⟩ := exists_isPosReflect_cfCollar hw hw0 hγ hs hc hsub hB hscale hδ hcol hfin
  have hlim := (hG.tendsto (mem_ball_self hδ : (x : ℂ) ∈ ball (x : ℂ) δ)).comp hcf
  have hlim' : Tendsto (fun v => c.1 (ρ v)) l (𝓝 (G x)) := hlim.congr' (hinside.mono fun v hv => by
    dsimp only [Function.comp_apply]
    rw [revChartInv_revChart hw hw0 hs (hsub hv)])
  have hval : G x = (y : ℂ) := tendsto_nhds_unique hlim' hchart
  have hxy : Tendsto (fun z => c.1 (revChartInv w s z)) (𝓝[H] (x : ℂ)) (𝓝 (y : ℂ)) := by
    rw [← hval]
    exact hG.tendsto (mem_ball_self hδ)
  exact tendsto_cfTransition hw hw0 hγ hs hc hsub hB hscale hδ hcol hfin (mem_ball_self hδ) hxy

end InteractingSLE.Sec5.Aux61GWindow20
