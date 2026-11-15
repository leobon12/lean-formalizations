/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TwoMeetInf
import InteractingSLE.Spec.Sec7.R5OutDomain

/-!
# R.6: the common-domain point for each two-outer-arm shape

PROVE-R6-TWO. The three shapes use their actual initial conformal charts
and actual relative hulls. The domain identities are obtained from the
landed outer-domain API. No shared-wall free-point assumption is needed
for this part of the argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H fwdHull)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Two

open Sec6 PocketTraversal PocketStopMarked Lemma71C
open PocketStopMarked.Outer

/-- The outer-domain identity specialized to a fixed initial chart. -/
theorem loewner_dom_eq_inter {B : Chart} (hB : B.IsConformal)
    {C : Set ℂ} {ψ : ℂ → ℂ} (hBdom : (B.dom : Set ℂ) = C) (hBfwd : EqOn B.1 ψ C)
    (hCH : C ⊆ H) (hψ : IsConformalBijection ψ C H) {γ : ℝ → ℂ}
    (hγ : IsDrivenCurve γ) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife γ) :
    ((B.loewner (fun s : ℝ => segDriver γ s.toNNReal) q).dom : Set ℂ) =
      C ∩ ψ ⁻¹' (H \ fwdHull (fun s : ℝ => segDriver γ s.toNNReal) q) := by
  have h := R5Out.current_dom_eq_relHull (A := (univ : Set Unit))
    (c := fun _ : Unit => B) (C := fun _ : Unit => C) (ψ := fun _ : Unit => ψ)
    (γ := fun _ : Unit => γ) (mem_univ ()) hq hγ hB hBdom hBfwd hCH hψ
  rw [HOuter.H_diff_relHull hCH] at h
  exact h

/-- The common point and time ordering for the bounded two-outer shape. -/
theorem exists_rat_relCharts_meet_two {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {xC yC xV yV : ℂ} {τC σC τV σV : ℝ} {ψ φ : ℂ → ℂ} {BC BV : Chart}
    (hC : IsOuterPocket W η C xC yC τC σC ψ)
    (hV : IsOuterPocket W η V xV yV τV σV φ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (trav η C τC σC ψ)) (hVC : V ⊆ C)
    (hBC : BC.IsConformal) (hBCdom : (BC.dom : Set ℂ) = C) (hBCfwd : EqOn BC.1 ψ C)
    (hBV : BV.IsConformal) (hBVdom : (BV.dom : Set ℂ) = V) (hBVfwd : EqOn BV.1 φ V)
    (htip : η (pocketFibre η C τC σC
      (clockOf (pocketClock η C τC σC σC) (capInv (trav η C τC σC ψ) q))) ∈ V)
    {ε : ℝ} (hε : 0 < ε) :
    let T := pocketFibre η C τC σC
      (clockOf (pocketClock η C τC σC σC) (capInv (trav η C τC σC ψ) q))
    ∃ q' : ℚ, relCap η V τV σV φ T < q' ∧
      (q' : ℝ) < relCap η V τV σV φ T + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (trav η V τV σV φ) ∧
      T < PocketStopWallsFin.ambTime0 η V τV σV φ (StripSys.rt q') ∧
      (((BV.loewner (fun s : ℝ => segDriver (trav η V τV σV φ) s.toNNReal)
        (StripSys.rt q')).dom : Set ℂ) ∩
        ((BC.loewner (fun s : ℝ => segDriver (trav η C τC σC ψ) s.toNNReal) q).dom : Set ℂ)).Nonempty :=
  exists_rat_meet_outer hC hV hq hVC hBV hBVdom hBVfwd
    (loewner_dom_eq_inter hBC hBCdom hBCfwd hC.subset_H hC.jordan.2.2.2.1 hC.driven hq) htip hε

/-- The common point and time ordering for the seed-opening outer, bounded inner shape. -/
theorem exists_rat_relCharts_meet_twoInf {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {yC xV yV : ℂ} {τC τV σV : ℝ} {ψ φ : ℂ → ℂ} {BC BV : Chart}
    (hC : IsOuterPocketInf W η C yC τC ψ)
    (hV : IsOuterPocket W η V xV yV τV σV φ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travInf η C τC ψ)) (hVC : V ⊆ C)
    (hBC : BC.IsConformal) (hBCdom : (BC.dom : Set ℂ) = C) (hBCfwd : EqOn BC.1 ψ C)
    (hBV : BV.IsConformal) (hBVdom : (BV.dom : Set ℂ) = V) (hBVfwd : EqOn BV.1 φ V)
    (htip : η (pocketFibreInf η C τC
      (clockOf (clockEnd η C τC) (capInv (travInf η C τC ψ) q))) ∈ V)
    {ε : ℝ} (hε : 0 < ε) :
    let T := pocketFibreInf η C τC
      (clockOf (clockEnd η C τC) (capInv (travInf η C τC ψ) q))
    ∃ q' : ℚ, relCap η V τV σV φ T < q' ∧
      (q' : ℝ) < relCap η V τV σV φ T + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (trav η V τV σV φ) ∧
      T < PocketStopWallsFin.ambTime0 η V τV σV φ (StripSys.rt q') ∧
      (((BV.loewner (fun s : ℝ => segDriver (trav η V τV σV φ) s.toNNReal)
        (StripSys.rt q')).dom : Set ℂ) ∩
        ((BC.loewner (fun s : ℝ => segDriver (travInf η C τC ψ) s.toNNReal) q).dom : Set ℂ)).Nonempty :=
  exists_rat_meet_outerInf hC hV hq hVC hBV hBVdom hBVfwd
    (loewner_dom_eq_inter hBC hBCdom hBCfwd hC.subset_H hC.jordan.2.2.2.1 hC.driven hq) htip hε

/-- The common point and time ordering for the two seed-opening outer shape. -/
theorem exists_rat_relCharts_meet_twoInfInf {W : ℝ → ℝ} {η : ℝ → ℂ} {C V : Set ℂ}
    {yC yV : ℂ} {τC τV : ℝ} {ψ φ : ℂ → ℂ} {BC BV : Chart}
    (hC : IsOuterPocketInf W η C yC τC ψ)
    (hV : IsOuterPocketInf W η V yV τV φ) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < capLife (travInf η C τC ψ)) (hVC : V ⊆ C)
    (hBC : BC.IsConformal) (hBCdom : (BC.dom : Set ℂ) = C) (hBCfwd : EqOn BC.1 ψ C)
    (hBV : BV.IsConformal) (hBVdom : (BV.dom : Set ℂ) = V) (hBVfwd : EqOn BV.1 φ V)
    (htip : η (pocketFibreInf η C τC
      (clockOf (clockEnd η C τC) (capInv (travInf η C τC ψ) q))) ∈ V)
    {ε : ℝ} (hε : 0 < ε) :
    let T := pocketFibreInf η C τC
      (clockOf (clockEnd η C τC) (capInv (travInf η C τC ψ) q))
    ∃ q' : ℚ, relCapInf η V τV φ T < q' ∧
      (q' : ℝ) < relCapInf η V τV φ T + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travInf η V τV φ) ∧
      T < PocketStopWallsFin.ambTime0Inf η V τV φ (StripSys.rt q') ∧
      (((BV.loewner (fun s : ℝ => segDriver (travInf η V τV φ) s.toNNReal)
        (StripSys.rt q')).dom : Set ℂ) ∩
        ((BC.loewner (fun s : ℝ => segDriver (travInf η C τC ψ) s.toNNReal) q).dom : Set ℂ)).Nonempty :=
  exists_rat_meet_outerInfInf hC hV hq hVC hBV hBVdom hBVfwd
    (loewner_dom_eq_inter hBC hBCdom hBCfwd hC.subset_H hC.jordan.2.2.2.1 hC.driven hq) htip hε

end InteractingSLE.Sec7.R6Two
