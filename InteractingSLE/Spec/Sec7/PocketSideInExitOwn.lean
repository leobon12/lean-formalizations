/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInExitActive

/-!
# A finite current access never lands at its own initial outgoing pole

PROVE-POCKET-SIDEIN. Retain the pole exclusion in the existing bounded
Jordan inverse extension, then compose with the actual finite own prefix.
No new boundary extension or pole argument is needed.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketStop PocketStopField PocketTraversal Lemma71C

/-- A point avoided by the entire initial inverse extension is also
avoided by every finite real landing after an actual own prefix. -/
theorem relative_landing_ne_of_initial_extension {Ω : Type*} {c : Ω → Chart}
    {γ : Ω → ℝ → ℂ} {q : ℝ≥0} {ω : Ω} (hγ : IsDrivenCurve (γ ω))
    (hq : (q : ℝ≥0∞) < capLife (γ ω)) {E : ℂ → ℂ}
    (hE : EqOn E (c ω).2.1 H) (hEc : ContinuousOn E Hbar) {p : ℂ}
    (hAvoid : ∀ z ∈ Hbar, E z ≠ p) {x : ℝ} {v : ℂ}
    (hLanding : Tendsto (relChart c γ q ω).2.1 (𝓝[H] (x : ℂ)) (𝓝 v)) : v ≠ p := by
  obtain ⟨F, hF, hFc, hFD⟩ := exists_relative_inverse_extension hγ hq hE hEc
  have hx : (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (by simp)
  have : (𝓝[H] (x : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hx)
  have hFlim := (((hFc _ hx).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
    (eventually_nhdsWithin_of_forall fun _ hz => hF hz)
  have heq := tendsto_nhds_unique hLanding hFlim
  intro hv
  obtain ⟨y, hy, hEy⟩ := hFD hx
  exact hAvoid y hy (hEy.trans (heq.symm.trans hv))

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketCoord Sec7.PocketJordan Sec7.PocketWordAssembly Sec7.PocketStopSide
  Sec7.PocketStop Sec7.PocketStopField Sec7.PocketTraversal Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω]

/-- At every live relative time, any finite real physical landing of a
bounded ready pocket avoids that pocket's own initial outgoing pole. -/
theorem relative_landing_ne_outgoingSeed {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) (hBounded : j.infinite = false)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) {x : ℝ} {p : ℂ}
    (hLanding : Tendsto (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1
      (𝓝[H] (x : ℂ)) (𝓝 p)) : p ≠ j.outgoingSeed d ω := by
  have hc := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  have hγ := isDrivenCurve_target hj ω hω
  have hω' := hω
  rw [target_event] at hω'
  have hJ := hj.2.2.2.2.2.2.2.2.2.2.1
  simp only [hBounded, Bool.false_eq_true, ↓reduceIte] at hJ
  have hcfg : IsCfPocketConfig (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed)
      (fun s : ℝ => d.driver s.toNNReal ω) (d.curve ω) := by
    rcases hj with ⟨-, -, -, -, -, hcfg, -, -, hAG, -⟩
    simp only [hBounded, Bool.false_eq_true, ↓reduceIte] at hAG
    exact hcfg ω (hAG hω').1 (hAG hω').2
  have hdom := hc.2.1
  rw [target_domain] at hdom
  have heq := hc.2.2.1
  rw [target_domain, target_chart] at heq
  obtain ⟨E, hE, hEc, hED⟩ := exists_inverse_extension_cfPocket hcfg (hJ ω hω') hc.1 hdom heq
  exact relative_landing_ne_of_initial_extension hγ hq hE hEc
    (fun z hz => (hED hz).2) hLanding

/-- The constructed actual original-visit landing avoids its own outgoing
corner at every real current coordinate. -/
theorem currentVisitLanding_ne_outgoingSeed {j : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hj : j.Ready d) (hBounded : j.infinite = false)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) (x : ℝ) :
    j.currentVisitLanding i d ω t x ≠ j.outgoingSeed d ω :=
  relative_landing_ne_outgoingSeed hj hBounded hRc hLc hω
    (visitCapacity_spec hj hω ht hvisit).2.1
    (tendsto_currentVisitLanding hj hRc hLc hω ht hvisit x)

end InteractingSLE.Wire.Current.SideTest
