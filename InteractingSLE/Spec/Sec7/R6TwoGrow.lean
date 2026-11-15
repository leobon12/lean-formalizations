/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoWall
import InteractingSLE.Spec.Sec7.PocketSideInPatchTip
import InteractingSLE.Spec.Sec7.HOuterMarkedPathInf

/-!
# R.6: fresh future points of a driven pocket traversal

PROVE-R6-TWO, continuation. The finite-horizon strict-growth theorem supplies
future trace points in the old active domain. This permits comparison of
the actual incident components without equating either with the full
ambient pocket complement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Two

open PocketTraversal Lemma71C

/-- Every positive live capacity interval of a driven traversal contains
a trace point in the domain at the earlier capacity. -/
theorem exists_capTrace_mem_domain {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : ENNReal.ofReal b < capLife γ) :
    ∃ s ∈ Ioc a b, capTrace γ s.toNNReal ∈
      H \ fwdHull (fun t : ℝ => segDriver γ t.toNNReal) a := by
  have hb0 : 0 ≤ b := ha.trans hab.le
  obtain ⟨c, hbc, hc⟩ := exists_real_btwn_of_lt (t := b.toNNReal)
    (by simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hb0] using hb)
  rw [Real.coe_toNNReal _ hb0] at hbc
  have hc0 : 0 ≤ c := hb0.trans hbc.le
  have hct : (c.toNNReal : ℝ≥0∞) < capLife γ := by
    simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hc0] using hc
  let d : ℝ := (b + c) / 2
  have hbd : b < d := by dsimp only [d]; linarith only [hbc]
  have hdc : d < c := by dsimp only [d]; linarith only [hbc]
  have hd0 : 0 ≤ d := hb0.trans hbd.le
  have hdc' : ENNReal.ofReal d < (c.toNNReal : ℝ≥0∞) := by
    simpa only [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hc0] using
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd0).2 hdc
  have hLT := (hγ.isGeneratingTrace hct).isLoewnerTraceLT hdc'
  have hW : Continuous (frozenDrive (segDriver γ) d) :=
    continuous_frozenDrive_of_lt hγ.segDriver_spec.2.1
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hd0).2 hdc |>.trans hc)
  have hW0 : frozenDrive (segDriver γ) d 0 = 0 := by
    rw [frozenDrive_zero hd0, hγ.segDriver_spec.1]
  obtain ⟨s, hs, hmem⟩ := hLT.exists_mem_diff hW hW0 ha hab hbd
  refine ⟨s, hs, ?_, ?_⟩
  · exact (QuantumZipper.fwdHull_mono (W := frozenDrive (segDriver γ) d)).2 b hmem.1
  · rw [fwdHull_eq_of_eqOn (W' := frozenDrive (segDriver γ) d) ha (hab.trans hbd)
      (fun t ht => (frozenDrive_eq ht).symm)]
    exact hmem.2

/-- Strict growth in the traversal's own time: every interval after `a`
contains a trace point in the unbounded complement of the prefix at `a`. -/
theorem exists_trace_mem_domain {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ s ∈ Ioc a b, γ s ∈ H \ fillH (γ '' Icc 0 a) := by
  have hb : 0 ≤ b := ha.trans hab.le
  obtain ⟨v, hv, hz⟩ := exists_capTrace_mem_domain hγ (hγ.capClock_nonneg ha)
    (hγ.strictMonoOn_capClock ha hb hab) (hγ.ofReal_capClock_lt hb)
  have hv0 : 0 ≤ v := (hγ.capClock_nonneg ha).trans hv.1.le
  have hs0 := capInv_nonneg γ v
  have hvs := (hγ.capInv_spec hv0
    ((ENNReal.ofReal_le_ofReal hv.2).trans_lt (hγ.ofReal_capClock_lt hb))).2
  have has : a < capInv γ v := by
    by_contra h
    have hm := hγ.strictMonoOn_capClock.monotoneOn hs0 ha (not_lt.1 h)
    rw [hvs] at hm
    exact (not_le_of_gt hv.1) hm
  have hsb : capInv γ v ≤ b := by
    by_contra h
    have hm := hγ.strictMonoOn_capClock hb hs0 (not_le.1 h)
    rw [hvs] at hm
    exact (not_lt_of_ge hv.2) hm
  refine ⟨capInv γ v, ⟨has, hsb⟩, ?_⟩
  rw [capTrace, Real.coe_toNNReal _ hv0, hγ.fwdHull_segDriver
    (hγ.capClock_nonneg ha) (hγ.ofReal_capClock_lt ha), hγ.capInv_eq ha] at hz
  exact hz

/-- An actual physical tip lies in the closure of the relative current
domain, with no simple-hull or one-to-one boundary correspondence assumed. -/
theorem tip_mem_closure_relChart_dom {B : Chart} (hB : B.IsConformal)
    {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife γ)
    {p : ℂ} (hp : p ∈ (B.dom : Set ℂ)) (hTrace : capTrace γ q = B.1 p) :
    p ∈ closure ((B.loewner (fun t : ℝ => segDriver γ t.toNNReal) q).dom : Set ℂ) := by
  have hconf := PocketStopSide.isConformal_relChart_of_driven
    (c := fun _ : Unit => B) (γ := fun _ : Unit => γ) (ω := ()) hγ hq hB
  have hlim := PocketStopSide.tendsto_relative_inverse_tip hB hγ hq hp hTrace
  have : (𝓝[H] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp only [Complex.zero_im]))
  exact mem_closure_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun _ hz => hconf.inv_mem_dom hz)

end InteractingSLE.Sec7.R6Two
