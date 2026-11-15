/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInPatchActualClock
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The canonical current inverse lands at the original trace tip

PROVE-POCKET-SIDEIN. The existing generating-trace tip limit applies to the
canonical local driver on a slightly longer live prefix. At an original
interior visit its physical composition lands at the original counterflow
point. Thus the canonical finite current extension at zero is that point.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketTraversal Lemma71C

/-- The existing generating-trace tip limit specialized to the canonical
driver of an arbitrary driven traversal, below its terminal capacity. -/
theorem tendsto_canonical_inverse_tip {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife γ) :
    Tendsto (QuantumZipper.fwdMapInv (fun s : ℝ => segDriver γ s.toNNReal) q)
      (𝓝[H] (0 : ℂ)) (𝓝 (capTrace γ q)) := by
  obtain ⟨T, hqT, hT⟩ := exists_real_btwn_of_lt hq
  have hT0 : 0 ≤ T := q.coe_nonneg.trans hqT.le
  have hT' : (T.toNNReal : ℝ≥0∞) < capLife γ := by
    rwa [ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ hT0]
  have hqT' : q < T.toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hT0]
    exact hqT
  exact (hγ.isGeneratingTrace hT').tendsto_fwdMapInv_tip
    (hγ.segDriver_spec.2.1.mono fun _ hs => hs.trans hT') hγ.segDriver_spec.1
    (ENNReal.coe_lt_coe.2 hqT')

/-- A tip whose initial chart lies in H has its physical inverse limit at
that same interior initial-domain point. -/
theorem tendsto_relative_inverse_tip {B : Chart} (hB : B.IsConformal)
    {γ : ℝ → ℂ} (hγ : IsDrivenCurve γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife γ)
    {p : ℂ} (hp : p ∈ (B.dom : Set ℂ)) (hTrace : capTrace γ q = B.1 p) :
    Tendsto (B.loewner (fun s : ℝ => segDriver γ s.toNNReal) q).2.1
      (𝓝[H] (0 : ℂ)) (𝓝 p) := by
  have hTip := tendsto_canonical_inverse_tip hγ hq
  rw [hTrace] at hTip
  have hInv : ContinuousAt B.2.1 (B.1 p) :=
    hB.1.continuousOn.continuousAt (QuantumZipper.isOpen_H.mem_nhds (hB.fwd_mem hp))
  have hComp := hInv.tendsto.comp hTip
  rw [hB.inv_fwd hp] at hComp
  exact hComp

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketTraversal Sec7.Lemma71C Sec7.PocketStop

variable {Ω : Type} [MeasurableSpace Ω]

/-- At an actual original interior visit, the actual current inverse at
the centered driver has the original counterflow point as its full H-limit. -/
theorem tendsto_current_inverse_zero {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) :
    Tendsto (relChart (j.target i d).baseChart (j.target i d).curve
      (j.visitCapacity d ω t).toNNReal ω).2.1 (𝓝[H] (0 : ℂ)) (𝓝 (d.curve ω t)) := by
  have hB := isDomainChart_baseChart hj hRc hLc hω
  have hp : d.curve ω t ∈ (((j.target i d).baseChart ω).dom : Set ℂ) := by
    rw [hB.coe_dom]
    exact hvisit
  exact tendsto_relative_inverse_tip hB.1 (isDrivenCurve_target hj ω hω)
    (visitCapacity_spec hj hω ht hvisit).2.1 hp
    (capTrace_target_visitCapacity hj hRc hLc hω ht hvisit)

/-- The canonical finite current extension at zero is the actual original
trace point; no independently chosen physical tip is introduced. -/
theorem currentVisitLanding_zero {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) :
    j.currentVisitLanding i d ω t 0 = d.curve ω t := by
  have : (𝓝[H] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  exact tendsto_nhds_unique (tendsto_currentVisitLanding hj hRc hLc hω ht hvisit 0)
    (tendsto_current_inverse_zero hj hRc hLc hω ht hvisit)

end InteractingSLE.Wire.Current.SideTest
