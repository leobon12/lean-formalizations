/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.CounterflowNoReturnRouteQ
import InteractingSLE.Spec.Wire.Thm12Inputs7
import InteractingSLE.Spec.Wire.Thm13Inputs7

/-!
# Theorems 1.2–1.3's input lists without Proposition 4.9's first-exit input

Packet PROVE-CFNORETURN3. Proposition 4.9's first exit in the chart `Q` (`Prop411Q.Prop49QExitStatement`, the input
`h49` of `Wire.theorem12Statement_of_open7`) follows from Zhan's Part A inputs at `16/κ`
(`Sec5.Prop49Exit.prop49QExitStatement_of_partA`), which the same wiring already takes (`hA`). So `h49` leaves the
input list of Theorem 1.2, and Theorem 1.3's `h411` (`Cond44Ref.Prop411QStatement`) reduces to Lemma 4.7 at rational
flow times and `hA`.

Conditional helpers (not providers). No result here uses Theorem 1.2, Theorem 1.3, `Theorem12ParamStatement`,
`Theorem13Statement`, two-seed completeness or Lemma 7.25 (R48).
-/

set_option autoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

/-- **Theorem 1.2 as `Exist.Theorem12Statement`** from `theorem12Statement_of_open7`'s inputs without `h49`
(Proposition 4.9's first exit, now from `hA`). -/
theorem theorem12Statement_of_open7_partA
    (hA : Sec5.PartAInputsSixteenDiv)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u}) : Exist.Theorem12Statement.{u} :=
  theorem12Statement_of_open7 hA h47 (Sec5.Prop49Exit.prop49QExitStatement_of_partA hA) hfirst hC4 hR7 hPW href725

/-- **Theorem 1.3 as `Exist.Theorem13Statement`** from `theorem13Statement_of_open7`'s inputs, with Proposition 4.11
in the chart `Q` (`h411`) replaced by Lemma 4.7 at rational flow times and Zhan's Part A inputs at `16/κ`. -/
theorem theorem13Statement_of_open7_partA
    (hA : Sec5.PartAInputsSixteenDiv)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ) : Exist.Theorem13Statement.{u} :=
  theorem13Statement_of_open7 (Sec5.Prop49Exit.prop411QStatement_of_lemma47Q_of_partA h47 hA) h51 hC4 hR7 hPW
    hA2 hA2'

end InteractingSLE.Wire
