/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutOffFront
import InteractingSLE.Spec.Sec7.R5LfReflect

/-!
# Protected ambient half-discs from exposed trace landings

PROVE-R5-OUTER, R98 §3.3. Nearby exposed coordinates land on the trace
prefix. If the terminal trace avoids their physical neighborhood, they
already land in the old hull. Reflection in the current coordinate then
gives an old ambient half-disc inside the current incident domain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R5Out

open R5Lift R5Ref

/-- A protected exposed interval covers an ambient half-disc at an old
prime end. The conclusion concerns the actual current domain and hence
also any raw union complement containing it. -/
theorem exists_ambient_halfDisc_of_local_trace_landing {cur : Chart}
    (hc : cur.IsConformal) {Fc : ℂ → ℂ} (hFc : EqOn Fc cur.2.1 H)
    (hFcc : ContinuousOn Fc Hbar) {η : ℝ → ℂ} {V : ℝ → ℝ}
    (hη : IsLoewnerTrace V η) (hV : Continuous V) (hV0 : V 0 = 0)
    {s T : ℝ} (hs : 0 ≤ s) (hK : (cur.dom : Set ℂ) ⊆ H \ fwdHull V s)
    {ξ : ℝ} {p : ℂ} (hp : Fc ξ = p) {r : ℝ} (hr : 0 < r)
    (hTail : Disjoint (η '' Icc s T) (closedBall p r))
    (hLand : ∃ r₀ > 0, ∀ u : ℝ, (u : ℂ) ∈ ball (ξ : ℂ) r₀ →
      Fc u ∈ η '' Icc 0 T ∧ Fc u ∈ H) :
    ∃ (v ρ : ℝ), 0 < ρ ∧
      Tendsto (fun z => fwdMap V s (cur.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (v : ℂ)) ∧
      fwdMapInv V s '' (H ∩ ball (v : ℂ) ρ) ⊆ cur.dom := by
  obtain ⟨r₀, hr₀, hLand⟩ := hLand
  have hξbar : (ξ : ℂ) ∈ Hbar := by change (0 : ℝ) ≤ (ξ : ℂ).im; simp
  obtain ⟨δ, hδ, hδF⟩ := Metric.tendsto_nhdsWithin_nhds.1 (hFcc _ hξbar).tendsto r hr
  set d := min r₀ δ
  have hd : 0 < d := lt_min hr₀ hδ
  have hOldLand : ∀ u : ℝ, (u : ℂ) ∈ ball (ξ : ℂ) d → Fc u ∈ fwdHull V s := by
    intro u hu
    obtain ⟨huTrace, huH⟩ := hLand u (ball_subset_ball (min_le_left _ _) hu)
    have huBall : Fc u ∈ closedBall p r := by
      apply ball_subset_closedBall
      rw [mem_ball, ← hp]
      exact hδF (show (u : ℂ) ∈ Hbar from by change (0 : ℝ) ≤ (u : ℂ).im; simp)
        (lt_of_lt_of_le (mem_ball.1 hu) (min_le_right _ _))
    exact mem_old_hull_of_trace_near hη hs hTail huTrace huBall huH
  obtain ⟨heq, hcont, hreal, hmaps, hinj, hdiff, hlim⟩ :=
    reflect_data_of_hull_landing hc hFc hFcc hη hV hV0 hs hK hOldLand
  set g := extendFrom H fun z => fwdMap V s (cur.2.1 z)
  have hgReal : (g ξ).im = 0 := hreal ξ (mem_ball_self hd) (by simp)
  have hgv : g ξ = ((g ξ).re : ℂ) := Complex.ext (by simp) (by simp [hgReal])
  obtain ⟨ρ, hρ, hCover⟩ := exists_halfBall_subset_image_of_reflect hd hdiff hcont hreal hmaps hinj
  refine ⟨(g ξ).re, ρ, hρ, ?_, ?_⟩
  · rw [← hgv]
    exact hlim ξ ⟨hξbar, mem_ball_self hd⟩
  · rintro _ ⟨z, hz, rfl⟩
    rw [← hgv] at hz
    obtain ⟨y, hy, hyz⟩ := hCover hz
    have hpoint := hK (hc.inv_mem_dom hy.1)
    have he : fwdMap V s (cur.2.1 y) = z := (heq hy).trans hyz
    rw [← he, QuantumZipper.RS.fwdMapInv_fwdMap hV hV0 hs hpoint]
    exact hc.inv_mem_dom hy.1

end InteractingSLE.Sec7.R5Out
