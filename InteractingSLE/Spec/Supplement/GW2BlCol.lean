/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BlTrace
import InteractingSLE.Spec.Supplement.GB6CoordBClock
import InteractingSLE.Spec.Supplement.GB6CoordBLocal
import InteractingSLE.Spec.Supplement.SB2VoCol
import InteractingSLE.Spec.Supplement.Q3RelGB6Chart

/-!
# Before contact: a real physical tip collides the relative labels it passes (D12 items 1–2, before contact)

Packet PROVE-GW2-BUF (round 9). Fix GB6's counterflow record driver `U`, the explored physical driver `w` with its
generating trace `γ`, and a horizon `T` before contact (`hd`: disjoint closed hulls). Then:

* **`relBdry_hull_of_relMap`**: a relative driver with the hulls `relMap '' fwdHull w t` (the version's hull identity)
  has the hulls of the `relBdry`-image of the physical prefix (`GB6.CoordB.exists_relBdry_prefix_driver`);
* **`mapsTo_relSafe`**: the physical prefix lies in `relSafe` (`GB6.CoordB.trace_mem_relSafe`);
* **`rightImg_eq_of_real_tip`**: at a physical time `τ ≤ T` where the physical trace is real, every relative label
  `x ≥ 0` at or left of `relBdry (γ τ)` collides with the relative driver at the relative clock `a τ`, provided the
  zero right gap stays open before. This combines this round's `relTrace` with NOJUMP's
  `SB.Vo.rightImg_eq_iff_real_tip`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Bh

open Supp8.GB6 Supp8.GB6.CoordB Restart MartChar.RealFlow

section Prefix

variable {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 < s)
  {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 p))
  {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0}
  (hd : Disjoint (closure (fwdHull U s)) (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (Ito.rpath w) T)))

include hU hU0 hs htip hw hw0 hγ hd in
/-- **The version's hull identity in the `relBdry` form**, before contact. -/
theorem relBdry_hull_of_relMap {R : ℝ → ℝ}
    (hR : ∀ t : ℝ≥0, t ≤ T → fwdHull R (relClock U s (Ito.rpath w) t) = relMap U s '' fwdHull (Ito.rpath w) t) :
    ∀ t : ℝ≥0, t ≤ T → fwdHull R (relClock U s (Ito.rpath w) t) = fillH (relBdry U s '' (γ '' Icc 0 t)) := by
  obtain ⟨V, -, -, hK⟩ := exists_relBdry_prefix_driver hU hU0 hs htip hw hw0 hγ hd
  intro t ht
  have htI : (t : ℝ) ∈ Icc (0 : ℝ) T := ⟨t.coe_nonneg, NNReal.coe_le_coe.2 ht⟩
  rw [hR t ht, ← (hK t htI).2.2, (hK t htI).2.1, ← image_Icc_toNNReal γ t, image_image]

include hU hs hw hw0 hγ hd in
/-- **The physical prefix lies in `relSafe` before contact.** -/
theorem mapsTo_relSafe : MapsTo γ (Iic T) (relSafe U s) := fun _ ht =>
  trace_mem_relSafe hU hs.le hw hw0 hγ (Supp8.Q3Rel.disjoint_closure_invHull hU hs.le hd) ht

end Prefix

/-- **A real physical tip collides every relative label it passes**, before contact. -/
theorem rightImg_eq_of_real_tip {U : ℝ → ℝ} (hU : Continuous U) (hU0 : U 0 = 0) {s : ℝ} (hs : 0 ≤ s)
    {γ : ℝ≥0 → ℂ} {a : ℝ≥0 → ℝ} {τ : ℝ≥0} (ha : IsClockOn a τ) (hγc : ContinuousOn γ (Iic τ)) (hγ0 : γ 0 = 0)
    (hsafe : MapsTo γ (Iic τ) (relSafe U s)) {R : ℝ → ℝ} (hRc : Continuous R) (hR0 : R 0 = 0)
    (hK : ∀ t ≤ τ, fwdHull R (a t) = fillH (relBdry U s '' (γ '' Icc 0 t))) (hσ : 0 < a τ)
    (hsep : ∀ t ∈ Ioo 0 (a τ), R t < rightImg R 0 t) (him : (γ τ).im = 0) (hne : relBdry U s (γ τ) ≠ 0)
    {x : ℝ} (hx : 0 ≤ x) (hxle : x ≤ (relBdry U s (γ τ)).re) :
    rightImg R x (a τ) = R (a τ) := by
  have hη := isLoewnerTraceLT_relTrace hU hU0 hs ha hγc hγ0 hsafe hK
  have hc := continuousOn_relTrace hU hU0 hs ha hγc hsafe
  have hend := relTrace_end (U := U) (s := s) (γ := γ) ha
  have hmem : γ τ ∈ relSafe U s := hsafe (le_refl τ)
  have hreal : γ τ = (((γ τ).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have himR : (relBdry U s (γ τ)).im = 0 := by
    rw [hreal]
    refine im_relBdry_of_real hU hU0 hs ?_
    rw [← hreal]
    exact hmem.2
  refine (SB.Vo.rightImg_eq_iff_real_tip hRc hR0 hσ hη hc hsep (by rw [hend]; exact hne) hx).2 ⟨?_, ?_⟩
  · rw [hend]; exact himR
  · rw [hend]; exact hxle

end InteractingSLE.Theorem14.GW2Bh
