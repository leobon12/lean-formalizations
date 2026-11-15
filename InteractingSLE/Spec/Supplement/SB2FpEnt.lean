/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FoEntry
import InteractingSLE.Spec.Supplement.SB2JRight
import InteractingSLE.Spec.Supplement.WalkIntCanonHull

/-!
# The right entry of a chart with a hull model

Worker PROVE-SB2-F3LAW (round 4). A chart `c` with a hull model `M` (`c.1 + M.shift` is the mapping-out function of
`M.hull`) has, at a real point free of the hull, the boundary value of the hull's mapping-out function shifted by
`−M.shift`; hence its right entry at a point `R` with a free ray to the right is `Fm.entry M.hull R − M.shift`.

* `bdryValue_eq_of_hullModel`, **`rightEntry_eq_of_hullModel`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Fp

open Fm

/-- **Boundary values of a chart with a hull model** are those of the hull's mapping-out function, shifted. -/
theorem bdryValue_eq_of_hullModel {c : Chart} (M : WalkIntCanon.HullModel c) {x r : ℝ} (hr : 0 < r)
    (hd : Disjoint (ball (x : ℂ) r) M.hull) :
    Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (((bdryVal M.hull x - M.shift : ℝ) : ℂ))) ∧
      Lx.bdryValue c x = bdryVal M.hull x - M.shift := by
  have heq := IsMapOut.eqOn M.isHull (ConformalImage.isMapOut_mapOut M.isHull) M.mapOut
  have hT := tendsto_mapOut_bdryVal M.isHull hr hd
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), ConformalImage.mapOut M.hull z - (M.shift : ℂ) = c.1 z := by
    filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds (mem_ball_self hr)), self_mem_nhdsWithin]
      with z hz hzH
    have hzA : z ∈ H \ M.hull := ⟨hzH, fun hzA => Set.disjoint_left.1 hd hz.2 hzA⟩
    rw [heq hzA]
    ring
  have hT' : Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (((bdryVal M.hull x - M.shift : ℝ) : ℂ))) := by
    refine Tendsto.congr' hev ?_
    push_cast
    exact hT.sub_const _
  exact ⟨hT', (Lx.tendsto_bdryValue hT' (by simp)).1.trans (by simp)⟩

/-- **The right entry of a chart with a hull model** free right of `R`: the hull's entry at `R`, shifted. -/
theorem rightEntry_eq_of_hullModel {c : Chart} (M : WalkIntCanon.HullModel c) {R : ℝ}
    (hR : FreeRight M.hull R) : Lx.rightEntry c R = entry M.hull R - M.shift := by
  have hT := (Fo.tendsto_bdryVal_entry M.isHull hR).sub_const M.shift
  have hev : ∀ᶠ x in 𝓝[>] R, bdryVal M.hull x - M.shift = Lx.bdryValue c x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨r, hr, hd⟩ := hR x hx
    exact ((bdryValue_eq_of_hullModel M hr hd).2).symm
  exact (hT.congr' hev).limUnder_eq

end InteractingSLE.Theorem14.SB.Fp
