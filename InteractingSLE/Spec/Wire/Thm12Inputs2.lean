/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm13Inputs2
import InteractingSLE.Spec.Sec7.LocalExtGStmt
import InteractingSLE.Spec.Sec7.DeterminationRestart
import InteractingSLE.Spec.Supplement.LPProbDetermination
import InteractingSLE.Spec.Supplement.R7Reference
import InteractingSLE.Spec.Sec7.Aux126
import InteractingSLE.WangWu.Theorem425

/-!
# Theorem 1.2 with the local extensions and the two-seed inputs plugged in

Packet PROVE-WIRE2 (no new mathematics). The frozen Theorem 1.2 (`exists_measurable_lifetime_trace_eq_comp_field`) now
follows, for every `κ > 0`, from three inputs at `κ` (PROVE-LOCEXT-B…G,
`LocalExt.exists_measurable_lifetime_trace_eq_comp_field_of_restartSeedCoupling`):

* `LP.TwoSeedGraphInput κ` (the two-seed reference input of Aux. lemma 55: determination and trace of every two-seed
  word with weights `> −2`);
* `LocalExt.StoppedSeedExtensionStatement κ` (Aux. lemma 54 for a stopped seed coupling; shared by the time-`0` and the
  restart extensions);
* `LocalExt.RestartSeedCouplingStatement κ` (Aux. lemma 53 with steps 3–5 of Aux. lemma 55 at a restart).

The two-seed input is split by range with the landed reductions:

* `κ < 4`: Proposition 7.3's determination and trace (`Determination.twoSeedGraphInput_of_prop73`); the trace from
  Lemma 7.1's pathwise pocket statement (`Wire.prop73TraceStatement_of_pocket2`);
* `κ = 4`: determination of the two-seed couplings and the boundary-hitting two-seed words
  (`WangWu.twoSeedGraphInput_four`, PROVE-WW-B9; Wang–Wu Proposition 4.24);
* `κ > 4`: Theorem R.7 and Lemma 7.25 (`LP.twoSeedGraphInput_of_inputs`), Theorem R.7's determination from its reference
  and the field-kernel statement (`R7.r7DeterminationStatement_of_inputs`), its trace from the reference
  (`R7.theoremR7TraceStatement_of_reference`), Lemma 7.25's trace from the pocket word evolutions
  (`Sec7.Aux126.lemma725TraceStatement_of_driverReference`,
  `Sec7.Lemma725Ref.lemma725DriverReferenceStatement_of_pocketWordEvolution`).

Wrappers (conditional helpers; neither is the provider): `exists_measurable_lifetime_trace_eq_comp_field_of_inputs2`
(three inputs per `κ`) and `exists_measurable_lifetime_trace_eq_comp_field_of_remaining2` (ten named inputs; four of
them — `hP`, `hhit`, `hR7`, `hPW` — are shared with Theorem 1.3's `Wire.ae_exists_isGeneratingTrace_of_remaining2`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Wire

/-- **The two-seed input for `0 < κ < 4`** from Proposition 7.3's determination and Lemma 7.1's pathwise pocket
statement. -/
theorem twoSeedGraphInput_of_lt_four2 (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0})
    (h73d : Determination.Prop73DeterminationStatement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    LP.TwoSeedGraphInput.{u} κ :=
  Determination.twoSeedGraphInput_of_prop73 h73d (prop73TraceStatement_of_pocket2 hP) hκ hκ4

/-- **The two-seed input for `κ > 4`** from Theorem R.7's reference and field kernel, Lemma 7.25's determination and
the pocket word evolutions of Lemma 7.25. -/
theorem twoSeedGraphInput_of_four_lt2 (hR7 : R7.R7ReferenceStatement.{0})
    (hK : R7.R7FieldKernelStatement.{0, u}) (h725d : LP.Lemma725DeterminationStatement.{u})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    {κ : ℝ} (hκ : 4 < κ) : LP.TwoSeedGraphInput.{u} κ :=
  LP.twoSeedGraphInput_of_inputs (R7.r7DeterminationStatement_of_inputs hR7 hK)
    (R7.theoremR7TraceStatement_of_reference hR7) h725d
    (Sec7.Aux126.lemma725TraceStatement_of_driverReference
      (Sec7.Lemma725Ref.lemma725DriverReferenceStatement_of_pocketWordEvolution hPW)) hκ

/-- **The two-seed input for every `κ > 0`** from the seven remaining named inputs of its three ranges. -/
theorem twoSeedGraphInput_of_remaining2 (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0})
    (h73d : Determination.Prop73DeterminationStatement.{u})
    (hdet4 : ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0}) (hK : R7.R7FieldKernelStatement.{0, u})
    (h725d : LP.Lemma725DeterminationStatement.{u})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    {κ : ℝ} (hκ : 0 < κ) : LP.TwoSeedGraphInput.{u} κ := by
  rcases lt_trichotomy κ 4 with h4 | rfl | h4
  · exact twoSeedGraphInput_of_lt_four2 hP h73d hκ h4
  · exact WangWu.twoSeedGraphInput_four hdet4 hhit
  · exact twoSeedGraphInput_of_four_lt2 hR7 hK h725d hPW h4

/-- **Theorem 1.2 (field determination)**, with exactly the conclusion of the frozen
`exists_measurable_lifetime_trace_eq_comp_field`, in the provider shape (all of the anchor's arguments implicit, its
hypotheses `hκ`, `hF`, `hcoup` auto-parameters), from the three inputs of Astra's §D.2 route at every `κ > 0`
(conditional helper; it is not the provider). -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_inputs2
    (h2 : ∀ κ : ℝ, 0 < κ → LP.TwoSeedGraphInput.{u} κ)
    (hext : ∀ κ : ℝ, 0 < κ → LocalExt.StoppedSeedExtensionStatement.{u} κ)
    (hrs : ∀ κ : ℝ, 0 < κ → LocalExt.RestartSeedCouplingStatement.{u} κ)
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
  LocalExt.exists_measurable_lifetime_trace_eq_comp_field_of_restartSeedCoupling hκ (h2 κ hκ) (hext κ hκ)
    (hrs κ hκ) hF hcoup

/-- **Theorem 1.2 (field determination)**, with exactly the conclusion of the frozen
`exists_measurable_lifetime_trace_eq_comp_field`, in the provider shape, from the **ten remaining** named inputs
(conditional helper; it is not the provider):

* `hP` — Lemma 7.1's pathwise pocket statement (also Theorem 1.3's);
* `h73d` — Proposition 7.3's determination of the two-seed couplings, `0 < κ < 4`;
* `hdet4` — determination of the two-seed couplings at `κ = 4` (Wang–Wu Proposition 4.24, determination part);
* `hhit` — the boundary-hitting two-seed words at `κ = 4` (also Theorem 1.3's);
* `hR7` — Theorem R.7's reference (also Theorem 1.3's);
* `hK` — Theorem R.7's common field kernel;
* `h725d` — Lemma 7.25's determination, `κ > 4`;
* `hPW` — the pocket word evolutions of Lemma 7.25 (also Theorem 1.3's);
* `hext` — Aux. lemma 54 for stopped seed couplings, every `κ > 0`;
* `hrs` — the restarted stopped seed coupling, every `κ > 0`. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_remaining2
    (hP : Sec7.Lemma71E.Lemma71PocketStatement.{0})
    (h73d : Determination.Prop73DeterminationStatement.{u})
    (hdet4 : ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      LP.HasFieldDeterminedHistories.{u} 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR))
    (hhit : WangWu.Theorem18.TwoSeedHittingStatement.{u} 4)
    (hR7 : R7.R7ReferenceStatement.{0}) (hK : R7.R7FieldKernelStatement.{0, u})
    (h725d : LP.Lemma725DeterminationStatement.{u})
    (hPW : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      Sec7.Lemma725Ref.PocketWordEvolution.{0} κ rL rR)
    (hext : ∀ κ : ℝ, 0 < κ → LocalExt.StoppedSeedExtensionStatement.{u} κ)
    (hrs : ∀ κ : ℝ, 0 < κ → LocalExt.RestartSeedCouplingStatement.{u} κ)
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
    (fun _ hκ' => twoSeedGraphInput_of_remaining2 hP h73d hdet4 hhit hR7 hK h725d hPW hκ') hext hrs hκ hF hcoup

end Wire

end InteractingSLE
