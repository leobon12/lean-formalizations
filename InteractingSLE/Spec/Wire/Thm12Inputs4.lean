/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12Inputs3
import InteractingSLE.Spec.Sec7.Aux50Ge8Main
import InteractingSLE.Spec.Sec7.LocalExtNPost
import InteractingSLE.Spec.Sec7.LocalExtOMain
import InteractingSLE.Spec.Sec7.Lemma72CMain
import InteractingSLE.Spec.Sec7.Lemma72BMain
import InteractingSLE.Spec.Sec7.Lemma613
import InteractingSLE.Spec.Sec7.Lemma725Det
import InteractingSLE.Spec.Sec5.Prop55N
import InteractingSLE.WangWu.ReverseContactS4Chain

/-!
# Theorem 1.2 with the results landed since PROVE-WIRE3 plugged in

Packet PROVE-WIRE4 (no new mathematics). PROVE-WIRE3 left Theorem 1.2
(`Wire.exists_measurable_lifetime_trace_eq_comp_field_of_open3`) with twelve named inputs. Since then:

* Aux. lemma 50 at the integer times holds for every `κ > 0` and all weights `> −2` (`Aux50Ge8.hasTraceStopKernel`,
  PROVE-AUX50B/AUX50C): `h50` and `h50R` are proved;
* Aux. lemma 54 (the stopped seed extension) is proved for every `κ > 0` (`LocalExt.stoppedSeedExtensionStatement`,
  PROVE-LOCEXT-N): `hPre` and `hLoc` are no longer needed;
* the restarted stopped seed coupling is proved for every `κ > 0` (`LocalExt.restartSeedCouplingStatement`,
  PROVE-LOCEXT-O): `hdl` is no longer needed;
* Lemma 7.25's determination follows from its trace statement and its reference
  (`Aux50Ge8.lemma725DeterminationStatement_of_reference`, PROVE-AUX50C), and the trace statement from the pocket
  word evolutions `hPW` (`Aux126.lemma725TraceStatement_of_driverReference`): `h725d` becomes `href725`;
* Lemma 7.1's joint statement follows from the pocket-conditional statement, the §4.2 reference, the half-plane
  Proposition 5.5 and Lemma 6.13 (`Lemma72B.lemma71JointStatement_of_pocketJoint`,
  `Lemma72C.pocketJointStatement_of_cond`);
  the reference and Proposition 5.5 follow from Propositions 4.11 and 5.1 in chart `Q`
  (`Cond44Ref.cond44ReferenceStatement_of_prop411Q`, `prop55HalfPlaneStatement_of_prop411Q_of_prop51Q`, PROVE-SEC5-N),
  and Lemma 6.13 from those two (`Lemma613.lemma613ContactStatement_of_prop55`, PROVE-LEMMA71J): `hJ` becomes
  `h411`, `h51`, `hPCond`;
* Wang–Wu's reverse-tip contact step follows from the image-driver statement
  (`WangWu.reverseTipContactStatement_of_imageDriver`, PROVE-WW-B15): `hcon` becomes `hImg`.

**Nine named inputs remain** (`exists_measurable_lifetime_trace_eq_comp_field_of_open4`). Each replaced input is
implied by its replacements through the landed reductions above, so nothing is strengthened.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- **Lemma 7.1's joint statement** (`κ < 4`) from Proposition 4.11 and Proposition 5.1 in chart `Q` and the
pocket-conditional statement: the §4.2 reference and the half-plane Proposition 5.5 from the first two (PROVE-SEC5-N),
Lemma 6.13 from those (PROVE-LEMMA71J), the pocket joint statement from the third (PROVE-LEMMA72C), and the delivery
of PROVE-LEMMA72B. -/
theorem lemma71JointStatement_of_open4 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (hPCond : Sec7.Lemma72C.PocketCondStatement.{u}) :
    Sec7.Lemma72.Lemma71JointStatement.{u} :=
  Sec7.Lemma72B.lemma71JointStatement_of_pocketJoint (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411)
    (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51)
    (Sec7.Lemma613.lemma613ContactStatement_of_prop55 (Sec5.Cond44Ref.cond44ReferenceStatement_of_prop411Q h411)
      (Sec5.Cond44Ref.prop55HalfPlaneStatement_of_prop411Q_of_prop51Q h411 h51))
    (Sec7.Lemma72C.pocketJointStatement_of_cond hPCond)

/-- **Aux. lemma 50 at the integer times for the boundary-hitting pairs, `0 < κ < 4`** (WIRE3's `h50`), proved
(PROVE-AUX50C). -/
theorem h50_of_open4 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
    (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) → Aux50.HasTraceStopKernel.{u, u} κ rL rR :=
  fun _ hκ _ _ _ hL hR _ => Aux50Ge8.hasTraceStopKernel hκ hL hR

/-- **Aux. lemma 50 at the integer times for the R.7 pairs, `κ > 4`** (WIRE3's `h50R`), proved (PROVE-AUX50C). -/
theorem h50R_of_open4 : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
    Aux50.HasTraceStopKernel.{0, u} κ rL rR :=
  fun _ hκ _ _ hL hR _ => Aux50Ge8.hasTraceStopKernel (by linarith) hL hR

/-- **Lemma 7.25's determination** (`κ > 4`) from its reference and the pocket word evolutions (which give its trace
statement): WIRE3's `h725d`. -/
theorem lemma725DeterminationStatement_of_open4
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u}) : LP.Lemma725DeterminationStatement.{u} :=
  Aux50Ge8.lemma725DeterminationStatement_of_reference
    (Sec7.Aux126.lemma725TraceStatement_of_driverReference
      (Sec7.Lemma725Ref.lemma725DriverReferenceStatement_of_pocketWordEvolution hPW)) href725

/-- **The two-seed input for every `κ > 0`** from the nine open named inputs of its three ranges:
`κ < 4`: `h411`, `h51`, `hPCond`; `κ = 4`: `hImg`, `hneg`, `hhit`; `κ > 4`: `hR7`, `hPW`, `href725`. -/
theorem twoSeedGraphInput_of_open4 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (hPCond : Sec7.Lemma72C.PocketCondStatement.{u})
    (hImg : WangWu.ImageDriverStatement.{0})
    (hneg : ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) : LP.TwoSeedGraphInput.{u} κ :=
  twoSeedGraphInput_of_open3 (lemma71JointStatement_of_open4 h411 h51 hPCond) h50_of_open4
    (WangWu.reverseTipContactStatement_of_imageDriver hImg) hneg hhit hR7 h50R_of_open4
    (lemma725DeterminationStatement_of_open4 hPW href725) hPW hκ

/-- **Lemma 7.5, universal form** (`Theorem15.Lemma75Statement`, Theorem 1.5's input) from the three `κ < 4` inputs
of Lemma 7.1's joint statement alone: Aux. lemma 50, Aux. lemma 54 and the restarted seed coupling are proved
(PROVE-AUX50C, PROVE-LOCEXT-N, PROVE-LOCEXT-O). It is `Aux50Hit.lemma75Statement_of_embeddedPair`. -/
theorem lemma75Statement_of_open4 (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) (hPCond : Sec7.Lemma72C.PocketCondStatement.{u}) :
    Theorem15.Lemma75Statement.{u} :=
  Aux50Hit.lemma75Statement_of_embeddedPair
    (prop73TraceStatement_of_joint3 (lemma71JointStatement_of_open4 h411 h51 hPCond))
    (Sec7.Lemma72.embeddedPairStatement_of_joint (lemma71JointStatement_of_open4 h411 h51 hPCond))
    (fun _ hκ _ => LocalExt.stoppedSeedExtensionStatement hκ) (fun _ hκ _ => LocalExt.restartSeedCouplingStatement hκ)

/-- **Theorem 1.2 (field determination)**, with exactly the conclusion of the frozen
`exists_measurable_lifetime_trace_eq_comp_field`, in the provider shape (all of the anchor's arguments implicit, its
hypotheses `hκ`, `hF`, `hcoup` auto-parameters), from the **nine open** named inputs (conditional helper; it is not
the provider):

* `h411` — Proposition 4.11 in Lemma 4.5's chart `Q` (`κ < 4`);
* `h51` — Proposition 5.1 in Proposition 5.5's configuration, chart `Q` (`κ < 4`);
* `hPCond` — Lemma 7.1's pocket construction with its chart clause and hull locality under conditioning on the
  exterior record (`κ < 4`);
* `hImg` — Wang–Wu's image driver at a random stop (`κ = 4`, nonnegative weights);
* `hneg` — determination of the two-seed couplings at `κ = 4` with a weight in `(−2, 0)`;
* `hhit` — the boundary-hitting two-seed words at `κ = 4` (also Theorem 1.3's);
* `hR7` — Theorem R.7's reference (`κ > 4`; also Theorem 1.3's);
* `hPW` — the pocket word evolutions of Lemma 7.25 (`κ > 4`; also Theorem 1.3's);
* `href725` — Lemma 7.25's reference with a field-determined history (`κ > 4`). -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_open4
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hPCond : Sec7.Lemma72C.PocketCondStatement.{u})
    (hImg : WangWu.ImageDriverStatement.{0})
    (hneg : ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u})
    {κ : ℝ} (hκ : 0 < κ := by assumption) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR := by assumption)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h := by assumption) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  exists_measurable_lifetime_trace_eq_comp_field_of_inputs2
    (fun _ hκ' => twoSeedGraphInput_of_open4 h411 h51 hPCond hImg hneg hhit hR7 hPW href725 hκ')
    (fun _ hκ' => LocalExt.stoppedSeedExtensionStatement hκ')
    (fun _ hκ' => LocalExt.restartSeedCouplingStatement hκ') hκ hF hcoup

/-- **Theorem 1.2 as the named form `Exist.Theorem12Statement`** (the frozen anchor's type), from the same nine open
inputs (conditional helper; for the consumers of the frozen type). -/
theorem theorem12Statement_of_open4
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u}) (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (hPCond : Sec7.Lemma72C.PocketCondStatement.{u})
    (hImg : WangWu.ImageDriverStatement.{0})
    (hneg : ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (href725 : Aux50Hit.Lemma725DetReferenceStatement.{u}) :
    Exist.Theorem12Statement.{u} := by
  intro _ hκ _ _ _ _ _ _ hF _ _ _ _ _ _ _ _ _ _ _ hcoup
  exact exists_measurable_lifetime_trace_eq_comp_field_of_open4 h411 h51 hPCond hImg hneg hhit hR7 hPW href725
    hκ hF hcoup

end Wire

end InteractingSLE
