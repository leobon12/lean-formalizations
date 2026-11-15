/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoDetourNoWrap
import InteractingSLE.Spec.Sec5.Prop51IQEast

/-!
# The new no-last-contact theorem on its actual small-gap regime

Below the critical gap, all excursion components are bounded above in time.
Consequently the finite-crosscut bypass alone supplies no-wrap on that regime.
The universal deterministic no-wrap statement is not inferred from an almost
sure theorem restricted to a regime of angles.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology

universe u

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- Direct reuse of `fwdNoLastContactQOn_smallGap`: every actual excursion
component is bounded above, almost surely at each positive rational hull time. -/
theorem gluedQ_bddAbove_excursionComponents_smallGap
    (hreg : Prop51Q.CfLineRegularQStatement.{u}) :
    GluedQ.{u} (fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) fun s η w =>
      ∀ t ∈ excursionTimes η w s,
        BddAbove (connectedComponentIn (excursionTimes η w s) t) :=
  (Prop51I.fwdNoLastContactQOn_smallGap hreg).mono fun _ _ _ hno _ ht =>
    bddAbove_excursionComponent_of_noLastContact hno ht

/-- The no-last-contact property also excludes the infinite-time alternative
of a positive end, leaving precisely a finite positive excursion endpoint. -/
theorem HasPositiveExcursionEnd.finite_of_noLastContact
    {η : ℝ → ℂ} {w : ℝ → ℝ} {s : ℝ} (hp : HasPositiveExcursionEnd η w s)
    (hno : NoLastCounterflowContact η w s) :
    ∃ a b x : ℝ, 0 < a ∧ a < b ∧ 0 < x ∧
      (∀ t ∈ Ico a b, η t ∈ QuantumZipper.H \ cfHullQ w s) ∧
      η b ∉ QuantumZipper.H \ cfHullQ w s ∧
      Tendsto (fun t => revChart w s (η t)) (𝓝[<] b) (𝓝 (x : ℂ)) := by
  rcases hp with hp | ⟨a, x, _ha, _hx, htail, _hlim⟩
  · exact hp
  · obtain ⟨v, hv, hnot⟩ := hno a
    exact (hnot (htail v hv)).elim

/-- On the small-gap regime, the actual no-last-contact theorem removes the
terminal bypass input. The finite-crosscut planar construction remains explicit. -/
theorem prop51QOn_smallGap_of_finiteCrosscutBypass
    (hreg : Prop51Q.CfLineRegularQStatement.{u})
    (hfinite : FiniteWesternCrosscutBypassStatement)
    (hbar : FwdFirstContactNotEastQOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) :
    Prop51QOn.{u} fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂ :=
  prop51QOn_of_gluedQ hreg
    (hbar.and (Prop51I.fwdNoLastContactQOn_smallGap hreg))
    fun _ _ _ _ hη hw hw0 hβ hs hnr hp =>
      negInv_notMem_leftSideOf_of_noLastContact_of_finiteCrosscutBypass hfinite
        hη hw hw0 hβ hs hnr hp.1 hp.2

/-- The forward probabilistic assembly needs no universal terminal-excursion
topology input: above the critical gap no contact is already proved, and below
it no last contact reduces the topology to the finite-crosscut bypass. This is
a conditional helper; neither planar bypass is asserted as a proved theorem. -/
theorem prop51QStatement_of_partA_of_eastSide_of_finiteCrosscutBypass
    (hA : PartAInputsSixteenDiv) (hfinite : FiniteWesternCrosscutBypassStatement)
    (hside : Prop51I.FwdPostContactEastSideQOn.{u}
      fun κ θ₁ θ₂ => ¬ IsLargeGap κ θ₁ θ₂) : Cond44Ref.Prop51QStatement.{u} := by
  have hreg := CfLineRegQ.cfLineRegularQStatement_of_partA hA
  apply prop51QStatement_of_on IsLargeGap (Prop51H.prop51QOn_largeGap_of_reg hreg)
  apply prop51QOn_smallGap_of_finiteCrosscutBypass hreg hfinite
  exact fwdFirstContactNotEastQOn_of_split (fwdFirstExitQOn_smallGap hreg)
    (Prop51H.fwdPostContactQOn_of_residual hreg
      (Prop51I.fwdPostContactEastQOn_of_side hreg hside))

end InteractingSLE.Sec5.Prop51HTopo
