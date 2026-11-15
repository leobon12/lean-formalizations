/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootI30Clock

/-!
# Literal capacity of the low-arc mapped trace

Packet PROVE-T14-GW2ROOT2. Adjoining the real boundary chart values
gives a compact continuous filling representative. Its upper part is
the visible mapped trace, so GW2's literal `capOf` equals the actual
Borel relative-clock reader.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootI30

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

/-- The intrinsic clock is also the literal capacity of the visible
mapped physical prefix, including at a positive low-arc root. -/
theorem capOf_mapped_prefix_eq_reader {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
    {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x)
    (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) e.2) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    ∀ t ∈ Icc 0 v,
      capOf (relMap (rdrv p.1) s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t ∩ H)) =
        RootH29.forwardCapacity x s t p := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let U := rdrv p.1
  let Γ := fun q => relBdry U s ((x : ℂ) + γ q)
  obtain ⟨V, hV, _, _, _, hK⟩ := exists_reader_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv
  have hrec := GaugeE.record_prefix_eq s hW0 hW.continuousOn
    (show (s : ℝ≥0∞) < ζ ω by rw [hζ]; exact ENNReal.coe_lt_top)
  have hmap : relMap U s = relMap (Ito.rpath (W · ω)) s :=
    relMap_eq_of_eqOn s.coe_nonneg hrec
  have hU : Continuous U := continuous_rdrv _
  have hU0 : U 0 = 0 := rdrv_zero _
  have hsafe : MapsTo (fun q => (x : ℂ) + γ q) (Icc 0 v) (relSafe U s) :=
    fun q hq => RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv hq.2
  have hphys : ContinuousOn (fun q => (x : ℂ) + γ q) (Icc 0 v) :=
    continuousOn_const.add (hγ.2.1.mono fun q hq =>
      (ENNReal.coe_le_coe.mpr hq.2).trans (lt_min_iff.mp hv).2.le)
  have hΓ : ContinuousOn Γ (Icc 0 v) :=
    (continuousOn_relBdry hU hU0 s.coe_nonneg).comp hphys hsafe
  have hΓ0 : (Γ 0).im = 0 := by
    have hz := hsafe (show (0 : ℝ≥0) ∈ Icc 0 v from ⟨zero_le, zero_le⟩)
    change (x : ℂ) + γ 0 ∈ relSafe U s at hz
    rw [hγ.1, add_zero] at hz
    change (relBdry U s ((x : ℂ) + γ 0)).im = 0
    rw [hγ.1, add_zero]
    exact im_relBdry_of_real hU hU0 s.coe_nonneg hz.2
  dsimp only
  intro t ht
  let K := RootH29.forwardHull x s t p
  have hfill := (hK t ht).2.2
  change IsFilling K
    (relMap (Ito.rpath (W · ω)) s '' ((fun q => γ q + x) '' Icc 0 t ∩ H)) at hfill
  rw [← hmap] at hfill
  have hcomm : (fun q => γ q + (x : ℂ)) = (fun q => (x : ℂ) + γ q) :=
    funext fun q => add_comm _ _
  rw [hcomm] at hfill
  have hsub : (fun q => (x : ℂ) + γ q) '' Icc 0 t ⊆ relSafe U s := by
    rintro _ ⟨q, hq, rfl⟩
    exact hsafe ⟨zero_le, hq.2.trans ht.2⟩
  have hfillΓ := isFilling_relBdry_image hU hU0 s.coe_nonneg hsub hfill
  rw [image_image] at hfillΓ
  have hΓt := hΓ.mono (Icc_subset_Icc_right ht.2)
  obtain ⟨hcomp, hb, ha, hf⟩ := RootD12.upper_prefix_geometry hΓt hΓ0.le
  have hHull : IsHPHull K := by
    change IsHPHull (RootH29.forwardHull x s t p)
    rw [← (hK t ht).2.1]
    exact isHPHull_fwdHull hV (RootH29.forwardCapacity_nonneg x s t p)
  have hfillEq : K = fillH (Γ '' Icc 0 t) :=
    (fillH_eq_iff_isFilling_of_isClosed hcomp.isBounded hcomp.isClosed hHull.1).1 hfillΓ
  have himage := image_relBdry_inter_H hU hU0 s.coe_nonneg hsub
  rw [image_image] at himage
  change capOf (relMap U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t ∩ H)) = _
  rw [← himage, RootC11.capOf_eq_hcapSet hb ha, hf, ← hfillEq]
  change ConformalImage.hcapSet K / 2 = (WholeField.hcapHit K).toReal / 2
  rw [WholeField.IsHPHull.hcapHit_eq hHull,
    ENNReal.toReal_ofReal (HPHull.hcap_nonneg ⟨_, hHull⟩), ConformalImage.hcapSet_eq hHull]

end InteractingSLE.Theorem14.GW2TipSystem.RootI30
