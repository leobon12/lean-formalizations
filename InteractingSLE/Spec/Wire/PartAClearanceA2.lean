/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.PartAClearanceTheorems
import InteractingSLE.Spec.ZhanGT4.G5FromA3
import InteractingSLE.Spec.Coupling.Assembly11BCoord

/-!
# Theorems 1.2 and 1.3 with Part A supplied by A.2

Packet PROVE-WIRE-PARTA. The clearance consumers need only the inverse-boundary
half of Part A. A.2 supplies that half through the first-swallow theorem A.3;
protected-ray clearance is already proved. The other open inputs are unchanged.
The universe adapter below lets Theorem 1.3 use its existing A.2 input both on
the original probability space and on the small spaces needed by Part A.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

universe u

namespace InteractingSLE.ZhanGT4.A35

/-- A.2 on spaces in universe `u` implies A.2 on small spaces, by lifting the
probability space and pulling back the evolution along `ULift.down`. -/
theorem threeForceCrosscutEightStatement_zero_of_lift {κ : ℝ}
    (hA2 : ThreeForceCrosscutEightStatement.{u} κ) :
    ThreeForceCrosscutEightStatement.{0} κ := by
  intro hκ x hx Ω mΩ P _ 𝓕 W VL VR B ζ hE
  let P' : Measure (ULift.{u} Ω) := P.map ULift.up
  have hmap : P'.map ULift.down = P := by
    change (P.map ULift.up).map ULift.down = P
    rw [Measure.map_map measurable_down measurable_up]
    exact Measure.map_id
  have hE' := Coupling.IsIntegratedSLEEvolution.comap measurable_down hmap hE
  have h := hA2 hκ x hx P' (Coupling.filtrationComap 𝓕 measurable_down)
    (fun t p => W t p.down) (fun i t p => VL i t p.down)
    (fun i t p => VR i t p.down) (fun t p => B t p.down) (fun p => ζ p.down) hE'
  exact (MeasurableEquiv.ulift.{0, u} (α := Ω)).symm.measurableEmbedding.ae_map_iff.mp h

end InteractingSLE.ZhanGT4.A35

namespace InteractingSLE.Wire

/-- Theorem 1.2's current input list with Part A derived from A.2. -/
theorem theorem12Statement_of_A2
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{0} κ)
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{u})
    (hfirst : Sec5.CfAvoidLeftQ.CfFirstContactQStatement.{u})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u}) : Exist.Theorem12Statement.{u} :=
  theorem12Statement_of_open7_partA_of_clearance
    (Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2 hA2')
    h47 hfirst hC4 hR7 hPW href725

/-- Theorem 1.3's current input list with Part A supplied by its existing A.2
inputs. The universe of the three-force assertion is unchanged. -/
theorem theorem13Statement_of_A2
    (h47 : Sec5.Prop411Q.Lemma47QHitStatement.{0})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{0})
    (hC4 : WangWu.Chamber4.Chamber4JointStatement.{u})
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR →
      rR < κ / 2 - 4 → Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hA2 : ∀ κ : ℝ, ZhanGT4.A34.FourForceCrosscutG3LifeStatement.{0} κ)
    (hA2' : ∀ κ : ℝ, ZhanGT4.A35.ThreeForceCrosscutEightStatement.{u} κ) :
    Exist.Theorem13Statement.{u} :=
  theorem13Statement_of_open7_partA_of_clearance
    (Sec5.partAInputsSixteenDivOfClearance_of_A2 hA2
      (fun κ => ZhanGT4.A35.threeForceCrosscutEightStatement_zero_of_lift (hA2' κ)))
    h47 h51 hC4 hR7 hPW hA2 hA2'

end InteractingSLE.Wire
