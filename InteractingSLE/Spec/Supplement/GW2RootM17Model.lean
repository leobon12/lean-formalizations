/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinChain
import InteractingSLE.Spec.Supplement.GB6CoordBClock
import InteractingSLE.Spec.Supplement.GW2RootF14Extension

/-!
# A complete relative trace through a protected physical prefix

Packet PROVE-T14-GW2ROOT2. Apply the SB2 finite-prefix trace extension to
GB6's driven relative boundary curve. Its boundary visits are included in
the trace. The global continuation agrees through a capacity buffer beyond
the required physical prefix, so locality preserves the actual hulls.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootM17

open Supp8.GB6 Sec7.PocketTraversal Sec7.Lemma71C

/-- A separated protected prefix has a complete relative generating
trace, with its exact intrinsic clock and hulls. -/
theorem exists_complete_relative_prefix {U : ℝ → ℝ}
    (hU : Continuous U) (hU0 : U 0 = 0) {σ : ℝ} (hσ : 0 < σ)
    {p : ℂ} (htip : Tendsto (QuantumZipper.fwdMapInv U σ) (𝓝[QuantumZipper.H] 0) (𝓝 p))
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ) {T : ℝ≥0} (hT : 0 < T)
    (hd : Disjoint (closure (QuantumZipper.fwdHull U σ))
      (closure ((fun z : ℂ => -z⁻¹) '' QuantumZipper.fwdHull (Ito.rpath w) T)))
    {B : ℝ≥0} (hBT : B < T) :
    ∃ (V : ℝ≥0 → ℝ) (Γ : ℝ≥0 → ℂ), Continuous V ∧ V 0 = 0 ∧
      IsGeneratingTrace V ⊤ Γ ∧
      relClock U σ (Ito.rpath w) 0 = 0 ∧
      StrictMonoOn (fun t : ℝ≥0 => relClock U σ (Ito.rpath w) t) (Icc 0 B) ∧
      ContinuousOn (fun t : ℝ≥0 => relClock U σ (Ito.rpath w) t) (Icc 0 B) ∧
      ∀ t ∈ Icc 0 B, QuantumZipper.fwdHull (Ito.rpath V) (relClock U σ (Ito.rpath w) t) =
        relMap U σ '' QuantumZipper.fwdHull (Ito.rpath w) t := by
  have hwr : Continuous (Ito.rpath w) := hw.comp continuous_real_toNNReal
  have hwr0 : Ito.rpath w 0 = 0 := by simpa only [Ito.rpath, Real.toNNReal_zero] using hw0
  have hfill : ∀ t ∈ Icc (0 : ℝ) T,
      IsFilling (QuantumZipper.fwdHull (Ito.rpath w) t) ((fun q : ℝ => γ q.toNNReal) '' Icc 0 t) := by
    intro t ht
    have hf := hγ.2.2 t.toNNReal ENNReal.coe_lt_top
    rwa [← image_Icc_toNNReal, Real.coe_toNNReal _ ht.1] at hf
  obtain ⟨_, _, _, ha0, ham, hac, hK⟩ :=
    exists_relChain_Icc hwr hwr0 hU hU0 hσ htip T.coe_nonneg hd hfill
  let ξ := CoordB.localCurve U σ γ T
  have hξ : IsDrivenCurve ξ := CoordB.isDrivenCurve_localCurve hU hU0 hσ htip hw hw0 hγ hT hd
  have hBL : ((relClock U σ (Ito.rpath w) B).toNNReal : ℝ≥0∞) < capLife ξ :=
    CoordB.relClock_lt_localLife hU hU0 hσ htip hw hw0 hγ hd hT hBT
  obtain ⟨b, hBb, hbL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hBL
  obtain ⟨c, hbc, hcL⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hbL
  have hgen := hξ.isGeneratingTrace hcL
  have hseg : ContinuousOn (segDriver ξ) {r | (r : ℝ≥0∞) < (c : ℝ≥0∞)} :=
    hξ.segDriver_spec.2.1.mono fun r hr =>
      show (r : ℝ≥0∞) < capLife ξ from (show (r : ℝ≥0∞) < (c : ℝ≥0∞) from hr).trans hcL
  obtain ⟨Wr, ηr, hWr, hWr0, hηr, he, _⟩ :=
    SB.FinRel.exists_globalTrace_of_isGeneratingTrace hgen hseg hξ.segDriver_spec.1 b.coe_nonneg
      (show ENNReal.ofReal (b : ℝ) < (c : ℝ≥0∞) by
        simpa only [ENNReal.ofReal_coe_nnreal] using hbc)
  have hew : EqOn (fun r : ℝ≥0 => Wr r)
      (fun r => CoordB.drivenDriver (fun _ : Unit => ξ) r ()) (Icc 0 b) := by
    intro r hr
    change Wr (r : ℝ) = CoordB.drivenDriver (fun _ : Unit => ξ) r ()
    have hrL : (r : ℝ≥0∞) < capLife ξ := (ENNReal.coe_le_coe.mpr hr.2).trans_lt hbL
    rw [CoordB.drivenDriver_eq (γ := fun _ : Unit => ξ) (ω := ()) hrL]
    simpa only [Real.toNNReal_coe] using (he r ⟨r.coe_nonneg, NNReal.coe_le_coe.mpr hr.2⟩).1
  refine ⟨(fun r => Wr r), (fun r => ηr r), hWr.comp NNReal.continuous_coe,
    ?_, Sec5.Prop513Bridge.generatingTrace_of_loewner hηr, ha0, ?_, ?_, ?_⟩
  · simpa only [NNReal.coe_zero] using hWr0
  · intro t ht u hu htu
    exact ham ⟨t.coe_nonneg, by exact_mod_cast ht.2.trans hBT.le⟩
      ⟨u.coe_nonneg, by exact_mod_cast hu.2.trans hBT.le⟩ (NNReal.coe_lt_coe.mpr htu)
  · exact hac.comp NNReal.continuous_coe.continuousOn
      (fun t ht => ⟨t.coe_nonneg, NNReal.coe_le_coe.mpr (ht.2.trans hBT.le)⟩)
  · intro t ht
    have htI : (t : ℝ) ∈ Icc (0 : ℝ) T :=
      ⟨t.coe_nonneg, NNReal.coe_le_coe.mpr (ht.2.trans hBT.le)⟩
    have ht0 := (hK t htI).1
    have hle : relClock U σ (Ito.rpath w) t ≤ relClock U σ (Ito.rpath w) B :=
      ham.monotoneOn htI ⟨B.coe_nonneg, NNReal.coe_le_coe.mpr hBT.le⟩ (NNReal.coe_le_coe.mpr ht.2)
    have htb : (relClock U σ (Ito.rpath w) t).toNNReal < b :=
      (Real.toNNReal_le_toNNReal hle).trans_lt (ENNReal.coe_lt_coe.mp hBb)
    have heK := RootF14.fwdHull_eq_of_prefix_eq hew htb
    rw [Real.coe_toNNReal _ ht0] at heK
    exact heK.trans (CoordB.fwdHull_localDriver hU hU0 hσ htip hw hw0 hγ hd hT (ht.2.trans_lt hBT))

end InteractingSLE.Theorem14.GW2TipSystem.RootM17
