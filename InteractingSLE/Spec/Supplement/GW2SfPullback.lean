/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SfChart
import InteractingSLE.Spec.Supplement.GW2SfHitSet

/-!
# Pulling the bad-boundary obstruction through an untouched chart

Packet PROVE-GW2-SAFE. Real-boundary conformality supplies a full relative
half-neighbourhood. Equality of the boundary heights and preservation of
the seed side identify the bad prefixes there. Finite exceptional sets
are harmless because the hitting set is a closure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Sf

open GW2Rd

/-- An untouched real chart preserving heights and the seed side preserves
avoidance of the closed bad-boundary set. -/
theorem notMem_hitSet_of_boundary_chart {κ θ : ℝ} (hκ : 0 < κ)
    {b bR : ℝ → ℝ} {J JR : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hbR : IsPiecewiseConstantBoundaryData bR JR)
    {φ : ℂ → ℂ} {x r : ℝ} (hr : 0 < r) (hφ : R16.IsRealBoundaryConformal φ x r)
    (hball : ball (x : ℂ) r ⊆ (hitSet κ b J θ)ᶜ)
    {E : Set ℝ} (hE : E.Finite) (hEJ : (J : Set ℝ) ⊆ E)
    (hside : ∀ u ∈ Ioo (x - r) (x + r), u ∉ E →
      (0 < u ↔ 0 < (φ u).re) ∧ (u < 0 ↔ (φ u).re < 0))
    (hheight : ∀ u ∈ Ioo (x - r) (x + r), u ∉ E → (φ u).re ∉ JR →
      bR (φ u).re = b u + θ * chiC κ) : φ x ∉ hitSet κ bR JR 0 := by
  let ER : Set ℝ := (JR : Set ℝ) ∪ (fun u : ℝ => (φ u).re) '' E
  have hER : ER.Finite := JR.finite_toSet.union (hE.image _)
  obtain ⟨ε, hε, hεim⟩ := Sec7.Aux37Side.exists_ball_image hφ (y := x) (Metric.mem_ball_self hr)
  intro hbad
  rw [hitSet_eq_closure_sdiff_finite hER] at hbad
  obtain ⟨q, ⟨y, ⟨hy, hyE⟩, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hbad ε hε
  obtain ⟨u, hub, -, hu, -, hu0⟩ := hεim (y : ℂ)
    (by simpa only [Metric.mem_ball, dist_comm] using hdist) (by simp)
  have huim : u.im = 0 := hu0 (by simp)
  have hue : u = (u.re : ℂ) := Complex.ext rfl (by simpa only [ofReal_im] using huim)
  have huI : u.re ∈ Ioo (x - r) (x + r) := Sec7.Aux37Side.ofReal_mem_ball_iff.1 (hue ▸ hub)
  have hφu : φ (u.re : ℂ) = (y : ℂ) := hue ▸ hu
  have hφur : (φ (u.re : ℂ)).re = y := by rw [hφu, ofReal_re]
  have hyJR : y ∉ JR := fun h => hyE (Or.inl h)
  have huE : u.re ∉ E := fun h => hyE (Or.inr ⟨u.re, h, hφur⟩)
  have huJ : u.re ∉ J := fun h => huE (hEJ h)
  have hheight' := hheight u.re huI huE (hφur ▸ hyJR)
  rw [hφur] at hheight'
  have hside' := hside u.re huI huE
  rw [hφur] at hside'
  apply hball hub
  rw [hue]
  apply ofReal_mem_hitSet
  rcases hy with hR | hL
  · have hupos : 0 < u.re := hside'.1.2 hR.1
    left
    refine ⟨hupos, ?_⟩
    rw [sum_filter_flowLineXR_le_theta hκ hb hupos huJ]
    have hsum := hR.2
    rw [sum_filter_flowLineXR_le_theta hκ hbR hR.1 hyJR] at hsum
    simpa only [zero_mul, add_zero, hheight'] using hsum
  · have huneg : u.re < 0 := hside'.2.2 hL.1
    right
    refine ⟨huneg, ?_⟩
    rw [sum_filter_le_flowLineXL_theta hκ hb huneg huJ]
    have hsum := hL.2
    rw [sum_filter_le_flowLineXL_theta hκ hbR hL.1 hyJR] at hsum
    simpa only [zero_mul, add_zero, hheight'] using hsum

end InteractingSLE.Theorem14.GW2Sf
