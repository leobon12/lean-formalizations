/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInInstHeight
import QuantumZipper.Proofs.Zipper.B5VSide
import QuantumZipper.Proofs.Loewner.RevMapExtension

/-!
# The inverse landing at a surviving original real side

PROVE-POCKET-SIDEIN. A surviving real forward trajectory, read backwards,
is the existing real reverse trajectory. Its holomorphic extension supplies
the full inverse boundary limit, rather than only a vertical limit.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H fwdMapInv)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The actual inverse chart lands at a surviving original real point.
This derives the inverse-landing premise of exact own-height transport. -/
theorem tendsto_inverse_of_surviving_real {W : ℝ → ℝ}
    (hW : Continuous W) (hW0 : W 0 = 0) {x T : ℝ} (hT : 0 ≤ T)
    {a : ℝ → ℂ} (hSurvives : QuantumZipper.IsForwardSol W x T a) :
    Tendsto (fwdMapInv W T) (𝓝[H] ((a T).re : ℂ)) (𝓝[H] (x : ℂ)) := by
  have hRev := QuantumZipper.B5.isRealRevSol_vrev_of_isForwardSol hT hSurvives
  have hV := QuantumZipper.B2.continuous_vrev hW T
  obtain ⟨c, hc, ρ, hρ, hgood⟩ :=
    QuantumZipper.RevMapExtension.exists_ball_isCRevSol hV hT hRev
  have hSol := QuantumZipper.RevMapExtension.isCRevSol_ofReal hRev
  have hdiff := QuantumZipper.RevMapExtension.hasDerivAt_revMapExt hT hρ hc hgood hSol
  have hvalue : QuantumZipper.RevMapExtension.revMapExt (QuantumZipper.B2.vrev W T) T
      ((a T).re : ℂ) = x := by
    rw [QuantumZipper.RevMapExtension.revMapExt_eq hSol hT, sub_self,
      QuantumZipper.FwdHolo.sol_zero hSurvives hT, hW0]
    simp
  have hlim := hdiff.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[H] ((a T).re : ℂ) ≤ 𝓝 ((a T).re : ℂ))
  rw [hvalue] at hlim
  refine tendsto_nhdsWithin_iff.2 ⟨hlim.congr' ?_, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with z hz
    rw [QuantumZipper.RevMapExtension.revMapExt_eq_revMap hV hT hz,
      QuantumZipper.B2.fwdMapInv_eq_revMap_vrev hW hW0 hT hz]
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hT hz

/-- Exact incoming height is preserved at the actual surviving real image,
with the inverse landing proved from the own flow. -/
theorem tendsto_exact_height_at_surviving_real {κ : ℝ} {c : Chart} (hc : c.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T x : ℝ} (hT : 0 ≤ T)
    {a : ℝ → ℂ} (hSurvives : QuantumZipper.IsForwardSol W x T a)
    {u vOld vNow : ℂ → ℝ} {b : ℝ}
    (hInitialHeight : Tendsto (sideMean κ c u vOld) (𝓝[H] (x : ℂ)) (𝓝 b))
    (hPhysicalGerm : Tendsto (fun z => vNow ((c.loewner W T).2.1 z) -
      vOld ((c.loewner W T).2.1 z)) (𝓝[H] ((a T).re : ℂ)) (𝓝 0)) :
    Tendsto (sideMean κ (c.loewner W T) u vNow)
      (𝓝[H] ((a T).re : ℂ)) (𝓝 b) :=
  tendsto_exact_height_of_own_loewner hc hW hT hSurvives
    (tendsto_inverse_of_surviving_real hW hW0 hT hSurvives) hInitialHeight hPhysicalGerm

end InteractingSLE.Sec7.PocketStopSide
