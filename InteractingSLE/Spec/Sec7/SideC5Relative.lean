/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC5Zero
import InteractingSLE.Spec.Sec7.SideC4Current

/-!
# Zero lift difference at fixed relative capacity

PROVE-SIDE-COLLAR2 continuation. The local continuous driver beyond the
current capacity works for every earlier capacity too. Thus Aux. 57 applies
to the literal old/current relative charts, including original-visit
references, with no finite boundary-map extension or lattice choice input.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PocketStopSide

open PocketStop PocketTraversal Lemma71C

/-- One continuous local driver represents both relative charts at ordered
live capacities. Their inherited logarithms use this same driver. -/
theorem exists_common_relChart_driver {Ω : Type*} {c : Ω → Chart}
    {γ : Ω → ℝ → ℂ} {ω : Ω} {p q : ℝ≥0}
    (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hpq : p ≤ q) :
    ∃ W : ℝ → ℝ, Continuous W ∧ W 0 = 0 ∧
      relChart c γ p ω = (c ω).loewner W p ∧
      relChart c γ q ω = (c ω).loewner W q := by
  obtain ⟨W, hW, hW0, q', hqq', hEq, hCurrent⟩ :=
    exists_relChart_eq_loewner (c := c) hγ hq
  refine ⟨W, hW, hW0, ?_, hCurrent⟩
  exact loewner_congr (c ω) p.coe_nonneg
    ((show (p : ℝ) ≤ q from hpq).trans_lt hqq') hEq

/-- Physical domains decrease along the relative capacity of one traversal. -/
theorem relChart_dom_antitone {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ}
    {ω : Ω} {p q : ℝ≥0} (hc : (c ω).IsConformal)
    (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hpq : p ≤ q) :
    ((relChart c γ q ω).dom : Set ℂ) ⊆ (relChart c γ p ω).dom := by
  obtain ⟨W, hW, hW0, hOld, hCurrent⟩ := exists_common_relChart_driver (c := c) hγ hq hpq
  rw [hOld, hCurrent]
  exact own_stage_dom_antitone hc hW hW0 p.coe_nonneg (show (p : ℝ) ≤ q from hpq)

/-- On an old inverse half-disc surviving to q, the inherited lift
difference is zero, for the actual relative charts. -/
theorem tendsto_relChart_lift_sub_zero {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ}
    {ω : Ω} {p q : ℝ≥0} (hc : (c ω).IsConformal)
    (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hpq : p ≤ q)
    {ξ x r : ℝ} (hr : 0 < r)
    (hCollar : (relChart c γ p ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
      ((relChart c γ q ω).dom : Set ℂ))
    (hTransition : Tendsto (fun z => (relChart c γ p ω).1 ((relChart c γ q ω).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ))) :
    Tendsto (fun z => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 z) -
      (relChart c γ p ω).2.2 ((relChart c γ q ω).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  obtain ⟨W, hW, hW0, hOld, hCurrent⟩ := exists_common_relChart_driver (c := c) hγ hq hpq
  rw [hOld, hCurrent] at hCollar hTransition ⊢
  exact tendsto_own_stage_lift_sub_zero hc hW hW0 p.coe_nonneg
    (show (p : ℝ) ≤ q from hpq) hr hCollar hTransition

end InteractingSLE.Sec7.PocketStopSide

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C

/-- An original-visit reference earlier in relative capacity has zero
inherited transition lift at every certified surviving incident half-disc. -/
theorem tendsto_referenceVisit_lift_sub_zero {Ω : Type} [MeasurableSpace Ω]
    {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω} (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife ((j.target i d).curve ω)) {s : ℝ}
    (hsq : (j.visitCapacity d ω s).toNNReal ≤ q) {ξ x r : ℝ} (hr : 0 < r)
    (hCollar : (j.referenceVisitChart i d ω s).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
      ((relChart (j.target i d).baseChart (j.target i d).curve q ω).dom : Set ℂ))
    (hTransition : Tendsto (fun z => (j.referenceVisitChart i d ω s).1
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ))) :
    Tendsto (fun z => (relChart (j.target i d).baseChart (j.target i d).curve q ω).2.2
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z) -
      (j.referenceVisitChart i d ω s).2.2
        ((relChart (j.target i d).baseChart (j.target i d).curve q ω).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 0) :=
  tendsto_relChart_lift_sub_zero (isDomainChart_baseChart hj hRc hLc hω).1
    (isDrivenCurve_target hj ω hω) hq hsq hr hCollar hTransition

end InteractingSLE.Wire.Current.SideTest
