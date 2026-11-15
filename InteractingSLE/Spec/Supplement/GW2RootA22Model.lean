/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootA22Clock
import InteractingSLE.Spec.Supplement.GW2RootY20Records

/-!
# The observable clock parametrizes the actual relative generating curve

Packet PROVE-T14-GW2ROOT2. Reuse GB6's boundary-extended driven curve on
a complete model of the original physical prefix. Its canonical capacity
trace agrees pointwise with the original charted tip at the proved clock.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2TipSystem.RootA22

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.CoordB
open Sec7.PocketTraversal Sec7.Lemma71C

/-- A driven relative curve with the exact physical tip at every time
through the protected cutoff. The clock is the concrete Borel reader. -/
theorem exists_driven_relative_tip_model {Ω : Type*}
    (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) (ζ ω) α)
    (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
    {s : ℝ≥0} (hsH : α s ∈ H)
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
    (hv : (v : ℝ≥0∞) < min
      (firstContactTime (fun q => sphereInv (γ q : OnePoint ℂ))
        ((fun q => (α q : OnePoint ℂ)) '' Icc 0 s)) e.2) :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    let a := fun t => RootZ21.forwardCapacity s t p
    ∃ ξ : ℝ → ℂ, IsDrivenCurve ξ ∧
      ((a v).toNNReal : ℝ≥0∞) < capLife ξ ∧
      ∀ t ∈ Icc 0 v, capTrace ξ (a t).toNNReal = relBdry (rdrv p.1) s (γ t) := by
  let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
  let U := rdrv p.1
  let a := fun t => RootZ21.forwardCapacity s t p
  have hs : (s : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  obtain ⟨D, hvD, hDS⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hv
  have hvD' : v < D := ENNReal.coe_lt_coe.mp hvD
  have hD : 0 < D := lt_of_le_of_lt zero_le hvD'
  obtain ⟨wc, γc, b, hDb, hwc, hwc0, hγc, hew, heγ⟩ :=
    RootF14.exists_complete_prefix_model hγ he.1 he.2.1 (lt_min_iff.mp hDS).2
  have hU : Continuous U := continuous_rdrv _
  have hU0 : U 0 = 0 := rdrv_zero _
  have hss : 0 < (s : ℝ) := by
    apply lt_of_le_of_ne s.coe_nonneg
    intro hz
    have hs0 : s = 0 := NNReal.coe_eq_zero.mp hz.symm
    exact ne_zero_of_mem_H hsH (by rw [hs0]; exact hα.1)
  have hprefix : EqOn U (Ito.rpath (W · ω)) (Icc 0 s) :=
    GaugeE.record_prefix_eq s hW0 hW.continuousOn hs
  have htip : Tendsto (QuantumZipper.fwdMapInv U s) (𝓝[H] 0) (𝓝 (α s)) := by
    apply (hα.tendsto_fwdMapInv_tip hW.continuousOn hW0 hs).congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (LP.fwdMapInv_eq_of_eqOn_Icc hU (hW.comp continuous_real_toNNReal)
      hU0 (by simpa only [Ito.rpath, Function.comp_apply, Real.toNNReal_zero] using hW0)
      s.coe_nonneg hprefix hz).symm
  have hd := disjoint_closure_fwdHull_of_lt_firstContactTime
    hα hW.continuousOn hW0 hγ he.1 he.2.1 hs
      (lt_min_iff.mp hDS).2 (lt_min_iff.mp hDS).1
  have hrecord : QuantumZipper.fwdHull U s =
      QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) s :=
    GaugeE.record_hull_eq s hW0 hW.continuousOn hs
  rw [← hrecord, ← RootF14.fwdHull_eq_of_prefix_eq hew hDb] at hd
  let ξ := localCurve U s γc D
  have hξ : IsDrivenCurve ξ := isDrivenCurve_localCurve hU hU0 hss htip hwc hwc0 hγc hD hd
  have hreg : Ito.rpath (regW s W ζ · ω) = Ito.rpath (W · ω) := by
    funext q
    exact regW_eq s hζ hW0 hW q.toNNReal
  have hclock : ∀ t ∈ Icc 0 v, a t = relClock U s (Ito.rpath wc) t := by
    intro t ht
    have hc := RootZ21.forwardCapacity_eq_relClock_before_contact
      W ζ ω hα hW.continuousOn hW0 hs hsH he hγ
        ((ENNReal.coe_le_coe.mpr ht.2).trans_lt hv)
    rw [hreg, ← GaugeE.record_relClock_eq s hW0 hW.continuousOn hs] at hc
    rw [show a t = RootZ21.forwardCapacity s t
        (cfRec s W ζ ω, recOf (t : ℝ≥0∞) e) from
      RootZ21.forwardCapacity_prefix_eq s _ he (lt_min_iff.mp hv).2 ht.2, hc]
    change ConformalImage.hcapSet (relMap U s '' QuantumZipper.fwdHull (Ito.rpath e.1) t) / 2 =
      ConformalImage.hcapSet (relMap U s '' QuantumZipper.fwdHull (Ito.rpath wc) t) / 2
    have hphys : QuantumZipper.fwdHull (Ito.rpath wc) t =
        QuantumZipper.fwdHull (Ito.rpath e.1) t :=
      RootF14.fwdHull_eq_of_prefix_eq hew ((ht.2.trans hvD'.le).trans_lt hDb)
    rw [hphys]
  refine ⟨ξ, hξ, ?_, ?_⟩
  · change ((a v).toNNReal : ℝ≥0∞) < capLife ξ
    rw [hclock v ⟨zero_le, le_rfl⟩]
    exact relClock_lt_localLife hU hU0 hss htip hwc hwc0 hγc hd hD hvD'
  · intro t ht
    change capTrace ξ (a t).toNNReal = relBdry U s (γ t)
    obtain ⟨q, hq0, hqt⟩ := exists_clockOf_eq (ht.2.trans_lt hvD')
    have hcap : capClock ξ q = a t := by
      rw [capClock_localCurve hU hU0 hss htip hwc hwc0 hγc hd hD hq0, hqt, ← hclock t ht]
    have ha : 0 ≤ a t := RootZ21.forwardCapacity_nonneg s t p
    rw [capTrace, Real.coe_toNNReal _ ha, ← hcap, hξ.capInv_eq hq0]
    change relBdry U s (γc (clockOf D q).toNNReal) = _
    rw [hqt, Real.toNNReal_coe, heγ ⟨zero_le, (ht.2.trans hvD'.le).trans hDb.le⟩]

end InteractingSLE.Theorem14.GW2TipSystem.RootA22
