/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm12Inputs2
import InteractingSLE.Spec.Sec7.Lemma71CTop
import InteractingSLE.Spec.Sec7.Lemma72
import InteractingSLE.Spec.Sec7.Aux50Kernel
import InteractingSLE.Spec.Sec7.Prop73Ref
import InteractingSLE.Spec.Sec7.LocalExtJMain
import InteractingSLE.Spec.Sec7.LocalExtKMain
import InteractingSLE.WangWu.Prop418RangeMain

/-!
# Theorem 1.2 with the results landed since PROVE-WIRE2 plugged in

Packet PROVE-WIRE3 (no new mathematics). PROVE-WIRE2 left Theorem 1.2
(`Wire.exists_measurable_lifetime_trace_eq_comp_field_of_remaining2`) with ten named inputs. Since then:

* Proposition 7.3's determination (`h73d`) follows from its reference coupling and Aux. lemma 50's field kernel for the
  boundary-hitting pairs (`Prop73Det.prop73DeterminationStatement_of_reference`, PROVE-PROP73D); the reference from
  Lemma 7.1's embedded pair (`Prop73Ref.prop73ReferenceStatement_of_embeddedPair`), the field kernel from Aux. lemma 50
  at the integer times (`Aux50.prop73FieldKernelStatement_of_aux50`) (PROVE-PROP73R); the embedded pair from Lemma 7.1's
  joint statement (`Sec7.Lemma72.embeddedPairStatement_of_joint`, PROVE-LEMMA72), which also gives the chart-form pocket
  statement (`lemma71PocketChartStatement_of_joint`), hence Proposition 7.3's trace: `hP` and `h73d` become `hJ`, `h50`;
* Theorem R.7's field kernel (`hK`) follows from Aux. lemma 50 at the integer times for the R.7 pairs
  (`Aux50.r7FieldKernelStatement_of_aux50`): `hK` becomes `h50R`;
* at `κ = 4` the determination of the nonnegative two-seed words follows from Wang–Wu's contact step
  (`WangWu.twoSeedGraphInput_four_of_contact`, PROVE-WW-B12): `hdet4` becomes `hcon` and `hneg` (weights in `(−2, 0)`);
* Aux. lemma 54 (`hext`) follows from (K-pre) and (Loc) (`LocalExt.stoppedSeedExtensionStatement_of_preLoc`,
  PROVE-LOCEXT-J; (U) and Theorem 2.2 on a standard Borel space are proved there);
* the restarted stopped seed coupling (`hrs`) follows from the driving law and locality under `Q`
  (`LocalExt.restartSeedCouplingStatement_of_input`, PROVE-LOCEXT-K).

**Twelve finer named inputs remain** (`exists_measurable_lifetime_trace_eq_comp_field_of_open3`). Every replaced input
is implied by its replacements through the landed reductions above, so nothing is strengthened.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- **Proposition 7.3's trace from Lemma 7.1's joint statement** (through the chart-form pocket statement). -/
theorem prop73TraceStatement_of_joint3 (hJ : Sec7.Lemma72.Lemma71JointStatement.{u}) :
    Sec7.Prop73TraceStatement.{u} :=
  Sec7.prop73TraceStatement_of_reference
    (Sec7.Lemma71C.lemma71TraceReferenceStatement_of_pocketChart (Sec7.Lemma72.lemma71PocketChartStatement_of_joint hJ))

/-- **Proposition 7.3's determination** (`0 < κ < 4`) from Lemma 7.1's joint statement and Aux. lemma 50 at the integer
times for the boundary-hitting pairs (PROVE-PROP73R with PROVE-LEMMA72). -/
theorem prop73DeterminationStatement_of_open3 (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR) :
    Determination.Prop73DeterminationStatement.{u} :=
  Prop73Ref.prop73DeterminationStatement_of_embeddedPair (prop73TraceStatement_of_joint3 hJ)
    (Sec7.Lemma72.embeddedPairStatement_of_joint hJ) h50

/-- **The two-seed input for `0 < κ < 4`** from Lemma 7.1's joint statement and Aux. lemma 50 for the boundary-hitting
pairs. -/
theorem twoSeedGraphInput_of_lt_four3 (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    LP.TwoSeedGraphInput.{u} κ :=
  Determination.twoSeedGraphInput_of_prop73 (prop73DeterminationStatement_of_open3 hJ h50)
    (prop73TraceStatement_of_joint3 hJ) hκ hκ4

/-- **The two-seed input for `κ > 4`** from Theorem R.7's reference, Aux. lemma 50 at the integer times for the R.7
pairs, Lemma 7.25's determination and the pocket word evolutions of Lemma 7.25. -/
theorem twoSeedGraphInput_of_four_lt3 (hR7 : R7.R7ReferenceStatement.{0})
    (h50R : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      Aux50.HasTraceStopKernel.{0, u} κ rL rR)
    (h725d : LP.Lemma725DeterminationStatement.{u})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    {κ : ℝ} (hκ : 4 < κ) : LP.TwoSeedGraphInput.{u} κ :=
  twoSeedGraphInput_of_four_lt2 hR7 (Aux50.r7FieldKernelStatement_of_aux50 h50R) h725d hPW hκ

/-- **The two-seed input for every `κ > 0`** from the nine named inputs of its three ranges. -/
theorem twoSeedGraphInput_of_open3 (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR)
    (hcon : WangWu.ReverseTipContactStatement.{0})
    (hneg : ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (h50R : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      Aux50.HasTraceStopKernel.{0, u} κ rL rR)
    (h725d : LP.Lemma725DeterminationStatement.{u})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    {κ : ℝ} (hκ : 0 < κ) : LP.TwoSeedGraphInput.{u} κ := by
  rcases lt_trichotomy κ 4 with h4 | rfl | h4
  · exact twoSeedGraphInput_of_lt_four3 hJ h50 hκ h4
  · exact WangWu.twoSeedGraphInput_four_of_contact hcon hneg hhit
  · exact twoSeedGraphInput_of_four_lt3 hR7 h50R h725d hPW h4

/-- **Aux. lemma 54 (the stopped seed extension)** from (K-pre) and (Loc) (PROVE-LOCEXT-J). -/
theorem stoppedSeedExtensionStatement_of_open3 {κ : ℝ} (hκ : 0 < κ)
    (hPre : LocalExt.ExtPreStopStatement.{u} κ) (hLoc : LocalExt.ExtLocalityStatement.{u} κ) :
    LocalExt.StoppedSeedExtensionStatement.{u} κ :=
  LocalExt.stoppedSeedExtensionStatement_of_preLoc hκ hPre hLoc

/-- **Lemma 7.5, universal form** (`Theorem15.Lemma75Statement`, Theorem 1.5's input) from Theorem 1.2's open inputs
for `0 < κ < 4` (Lemma 7.1's joint statement, Aux. lemma 50 for the boundary-hitting pairs, (K-pre), (Loc) and the
driving law and locality under `Q`), through PROVE-PROP73D's Lemma 7.5 bridge
(`Prop73Ref.lemma75Statement_of_embeddedPair`).
-/
theorem lemma75Statement_of_open3 (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR)
    (hPre : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtPreStopStatement.{u} κ)
    (hLoc : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.ExtLocalityStatement.{u} κ)
    (hdl : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartDrivingLocalityInput.{u} κ) :
    Theorem15.Lemma75Statement.{u} :=
  Prop73Ref.lemma75Statement_of_embeddedPair (prop73TraceStatement_of_joint3 hJ)
    (Sec7.Lemma72.embeddedPairStatement_of_joint hJ) h50
    (fun κ hκ hκ4 => stoppedSeedExtensionStatement_of_open3 hκ (hPre κ hκ hκ4) (hLoc κ hκ hκ4))
    (fun κ hκ hκ4 => LocalExt.restartSeedCouplingStatement_of_input hκ (hdl κ hκ hκ4))

/-- **Theorem 1.2 (field determination)**, with exactly the conclusion of the frozen
`exists_measurable_lifetime_trace_eq_comp_field`, in the provider shape (all of the anchor's arguments implicit, its
hypotheses `hκ`, `hF`, `hcoup` auto-parameters), from the **twelve open** named inputs (conditional helper; it is not
the provider):

* `hJ` — Lemma 7.1's joint statement (embedded pair and chart-form pocket; `κ < 4`);
* `h50` — Aux. lemma 50 at the integer times, boundary-hitting two-seed pairs, `0 < κ < 4`;
* `hcon` — Wang–Wu's reverse-tip contact step (`κ = 4`, nonnegative weights);
* `hneg` — determination of the two-seed couplings at `κ = 4` with a weight in `(−2, 0)`;
* `hhit` — the boundary-hitting two-seed words at `κ = 4` (also Theorem 1.3's);
* `hR7` — Theorem R.7's reference (also Theorem 1.3's);
* `h50R` — Aux. lemma 50 at the integer times for the R.7 pairs, `κ > 4`;
* `h725d` — Lemma 7.25's determination, `κ > 4`;
* `hPW` — the pocket word evolutions of Lemma 7.25 (also Theorem 1.3's);
* `hPre`, `hLoc` — (K-pre) and (Loc) of Aux. lemma 54, every `κ > 0`;
* `hdl` — the driving law and locality under `Q` of the restarted seed coupling, every `κ > 0`. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_open3
    (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR)
    (hcon : WangWu.ReverseTipContactStatement.{0})
    (hneg : ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (h50R : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      Aux50.HasTraceStopKernel.{0, u} κ rL rR)
    (h725d : LP.Lemma725DeterminationStatement.{u})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hPre : ∀ κ : ℝ, 0 < κ → LocalExt.ExtPreStopStatement.{u} κ)
    (hLoc : ∀ κ : ℝ, 0 < κ → LocalExt.ExtLocalityStatement.{u} κ)
    (hdl : ∀ κ : ℝ, 0 < κ → LocalExt.RestartDrivingLocalityInput.{u} κ)
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
    (fun _ hκ' => twoSeedGraphInput_of_open3 hJ h50 hcon hneg hhit hR7 h50R h725d hPW hκ')
    (fun κ' hκ' => stoppedSeedExtensionStatement_of_open3 hκ' (hPre κ' hκ') (hLoc κ' hκ'))
    (fun κ' hκ' => LocalExt.restartSeedCouplingStatement_of_input hκ' (hdl κ' hκ')) hκ hF hcoup

/-- **Theorem 1.2 as the named form `Exist.Theorem12Statement`** (the frozen anchor's type), from the same twelve open
inputs (conditional helper; for the consumers of the frozen type). -/
theorem theorem12Statement_of_open3
    (hJ : Sec7.Lemma72.Lemma71JointStatement.{u})
    (h50 : ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
      Aux50.HasTraceStopKernel.{u, u} κ rL rR)
    (hcon : WangWu.ReverseTipContactStatement.{0})
    (hneg : ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < 0 ∨ rR < 0) →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0})
    (h50R : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
      Aux50.HasTraceStopKernel.{0, u} κ rL rR)
    (h725d : LP.Lemma725DeterminationStatement.{u})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hPre : ∀ κ : ℝ, 0 < κ → LocalExt.ExtPreStopStatement.{u} κ)
    (hLoc : ∀ κ : ℝ, 0 < κ → LocalExt.ExtLocalityStatement.{u} κ)
    (hdl : ∀ κ : ℝ, 0 < κ → LocalExt.RestartDrivingLocalityInput.{u} κ) :
    Exist.Theorem12Statement.{u} := by
  intro _ hκ _ _ _ _ _ _ hF _ _ _ _ _ _ _ _ _ _ _ hcoup
  exact exists_measurable_lifetime_trace_eq_comp_field_of_open3 hJ h50 hcon hneg hhit hR7 h50R h725d hPW hPre hLoc
    hdl hκ hF hcoup

end Wire

end InteractingSLE
