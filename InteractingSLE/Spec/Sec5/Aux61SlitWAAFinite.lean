/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GNextCompleted
import InteractingSLE.WangWu.ChamberSides

/-! # A completed finite physical access avoids the inverse Cayley pole

The bounded inverse at the selected endpoint is the Cayley image of the
physical endpoint. The same identity holds on the completed access, so
the whole completed segment lies in an open pole-free neighborhood.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61SlitWAA
open Aux61FibData Aux61GInst Aux61GNext

/-- The ambient plane with the inverse Cayley pole's closed-half-plane
fibre removed; points below the real axis impose no inverse condition. -/
def poleFreeRegion (F : ℂ → ℂ) : Set ℂ := (Hbar ∩ F ⁻¹' {1})ᶜ

theorem isOpen_poleFreeRegion {F : ℂ → ℂ} (hF : ContinuousOn F Hbar) :
    IsOpen (poleFreeRegion F) :=
  (hF.preimage_isClosed_of_isClosed QuantumZipper.isClosed_Hbar isClosed_singleton).isOpen_compl

variable {X : Type*} [MeasurableSpace X] {E : Set X} {c : X → Chart}
  {ρ : X → ℝ≥0 → ℂ} {T : X → ℝ≥0∞}

/-- Continuity of the bounded inverse at a finite selected real limit
identifies that boundary value with the actual finite physical contact. -/
theorem boundedInverse_eq_at_endpoint (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤)
    (hF : ContinuousOn (boundedInverse (c x)) Hbar) {y : ℝ}
    (hend : Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ))) :
    boundedInverse (c x) (y : ℂ) = cayley (ρ x (T x).toNNReal) := by
  have he0 : 0 < (T x).toNNReal := ENNReal.toNNReal_pos hpos.ne' hfin.ne
  have heT := ENNReal.coe_toNNReal hfin.ne
  have : (𝓝[<] (T x).toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, he0⟩
  have hbar : ∀ᶠ u in 𝓝[<] (T x).toNNReal, inPath E c ρ T x u ∈ Hbar := by
    filter_upwards [Ioo_mem_nhdsLT he0] with u hu
    have huT : (u : ℝ≥0∞) < T x := heT ▸ ENNReal.coe_lt_coe.2 hu.2
    rw [hs.inPath_eq_fwd hx hu.1 huT]
    exact QuantumZipper.H_subset_Hbar ((hs.conf x hx).fwd_mem (hs.inside x hx u hu.1 huT))
  have hybar : (y : ℂ) ∈ Hbar := by change 0 ≤ (y : ℂ).im; simp only [Complex.ofReal_im, le_refl]
  exact tendsto_nhds_unique ((hF _ hybar).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hend, hbar⟩))
    (tendsto_boundedInverse_inPath_at_contact hs hx hpos hfin)

/-- The whole completed access avoids the physical-infinity pole, with
no finite-buffer hypothesis. This includes both real endpoint values. -/
theorem completed_access_avoids_pole (hs : IsRestartSpec E c ρ T) {x : X} (hx : x ∈ E)
    (hpos : 0 < T x) (hfin : T x < ⊤)
    (hF : ContinuousOn (boundedInverse (c x)) Hbar) {y : ℝ}
    (hend : Tendsto (inPath E c ρ T x) (𝓝[<] (T x).toNNReal) (𝓝 (y : ℂ)))
    {γ : ℝ≥0 → ℂ} (hγeq : EqOn γ (inPath E c ρ T x) (Iio (T x).toNNReal))
    (hγ0 : γ 0 = 0) (hγend : γ (T x).toNNReal = (y : ℂ)) :
    ∀ u ∈ Iic (T x).toNNReal, boundedInverse (c x) (γ u) ≠ 1 := by
  have hc := hs.conf x hx
  have heq := boundedInverse_eqOn_of_conformal hc
  have heT := ENNReal.coe_toNNReal hfin.ne
  have hzero : ρ x 0 ∈ Hbar := closure_H ▸ closure_mono hc.dom_subset (hs.start_mem x hx)
  have hlast : ρ x (T x).toNNReal ∈ Hbar := closure_H ▸ closure_mono hc.dom_subset
    (hs.mem_closure_at_T (mem_exitEv_of_finite hx hpos hfin (V := univ)) hfin)
  intro u hu
  rcases lt_or_eq_of_le (mem_Iic.1 hu) with hue | rfl
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu0 | hu0
    · rw [← hu0, hγ0, boundedInverse_zero_of_restartSpec hs hx hpos heq hF]
      exact WangWu.cayley_ne_one_of_Hbar hzero
    · have huT : (u : ℝ≥0∞) < T x := heT ▸ ENNReal.coe_lt_coe.2 hue
      have huD := hs.inside x hx u hu0 huT
      rw [hγeq hue, hs.inPath_eq_fwd hx hu0 huT, heq (hc.fwd_mem huD),
        Function.comp_apply, hc.inv_fwd huD]
      exact WangWu.cayley_ne_one_of_Hbar (QuantumZipper.H_subset_Hbar (hc.dom_subset huD))
  · rw [hγend, boundedInverse_eq_at_endpoint hs hx hpos hfin hF hend]
    exact WangWu.cayley_ne_one_of_Hbar hlast

end InteractingSLE.Sec5.Aux61SlitWAA
