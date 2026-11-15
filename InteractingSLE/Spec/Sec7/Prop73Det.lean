/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.DeterminationRestart
import InteractingSLE.Spec.Supplement.R7Reference
import InteractingSLE.Spec.Sec4.Thm12Special
import InteractingSLE.Spec.Supplement.LP1Seed
import InteractingSLE.WangWu.Theorem18
import InteractingSLE.Spec.Sec7.LocalExtGStmt
import InteractingSLE.Spec.Sec7.Lemma75Bridge

/-!
# Proposition 7.3, determination: from the embedded reference and the field kernel

Packet PROVE-PROP73D, item (2). Specification §7.1, Proposition 7.3 and its proof (`source/spec/p241-288.md` L37–L44,
pp. 242–243):

> In every coupling satisfying the original optional outside-hull specification of Theorem 1.1, the curve is
> determined by its field. All these couplings have the same full field–curve joint law and the same determining
> function up to a set of zero GFF probability.
>
> *Proof.* The embedded construction has produced one pair in which the field determines the curve […]. Consider any
> other coupling with the original optional local-set and outside-hull specification. Integrated driving uniqueness
> gives it the same continuous trace law. […] **Aux.** lemma 51 identifies its full field–history joint law through
> each deterministic capacity time `n` with that of the constructed reference. […] In the constructed reference that
> law is concentrated on the graph of a measurable function of the field. The identical joint law in every original
> coupling is concentrated on the same graph.

So the proof has two inputs, the **reference** (Lemma 7.1 with Lemma 7.2 and the remark on p. 227: "The embedded
construction therefore covers every admissible two-seed pair") and the **identification of the joint law** (Aux.
lemmas 50–51), and one transfer step, already in Lean (`LawUnique.hasFieldDeterminedHistories_of_isOptionalHullLawUnique`).

This file proves `Determination.Prop73DeterminationStatement` (the named input of LOCEXT's Lemma 7.5 and of the
Theorem 1.2 wiring, unowned before this packet) from

* `Prop73ReferenceStatement` (**named input**: the embedded reference of Lemmas 7.1–7.2), and
* `Prop73FieldKernelStatement` (**named input**: Aux. lemma 50's common field kernel for the two-seed words, needed
  only for the **boundary-hitting** pairs, `min(ρ^L, ρ^R) < κ/2 − 2`), with
* `Sec7.Prop73TraceStatement` (the trace part of Proposition 7.3, an existing named input; it is the finite-time
  continuity that Aux. lemma 51 assumes, again only for the boundary-hitting pairs).

For the **non-boundary-intersecting pairs** (`ρ^L, ρ^R ≥ κ/2 − 2`) the identification of the joint law is already
proved (Aux. lemma 23 for words with admissible partial sums, `Sec4.isOptionalHullLawUnique_of_admissible`: the trace
is simple, in `ℍ` and thin), so the reference is the only input there
(`hasFieldDeterminedHistories_twoSeed_of_admissible`). For the boundary-hitting pairs the identification is the
two-seed form of Aux. lemma 50 with the integrated driving uniqueness of Theorem 2.2, exactly as for Theorem R.7 at
`κ > 4` (`R7.hasFieldDeterminedHistories_twoSeed_of_reference`, reused here; it is stated for every `κ > 0`).

## Main results

* `hasFieldDeterminedHistories_twoSeed_of_admissible`: non-boundary-intersecting pairs, from one reference coupling;
* `hasFieldDeterminedHistories_twoSeed_of_kernel`: boundary-hitting pairs, from one reference coupling, the trace part
  and the field kernel;
* **`prop73DeterminationStatement_of_reference`**: `Determination.Prop73DeterminationStatement` from
  `Prop73ReferenceStatement`, `Prop73FieldKernelStatement` and `Sec7.Prop73TraceStatement`;
* `lemma75DeterminationStatement_of_reference`, `lemma75Statement_of_reference`: Lemma 7.5 per coupling (LP11's input)
  and in its universal form (Theorem 1.5's input, through `Lemma75Bridge`) from these inputs and LOCEXT's
  inputs of Aux. lemmas 53–55.

## Why not two conditionally independent copies

The packet suggested a different route (two copies of the curve conditionally independent given the field, each on
the right of the other by a monotonicity statement from Lemma 7.1). The specification does not argue this way and no
landed statement supplies the needed ordering of two copies at the **same** angle: Proposition 7.4 (and Proposition
5.5, `Sec5.prop55_of_prop51`) order flow lines of **distinct** angles `θ₁ < θ₂`, and Proposition 7.4 is applied to
the flow lines after Proposition 7.3 has made them functions of the field (p. 243: "The flow lines … are consequently
well-defined path-valued functions of their fields … Applying the same component-pair construction simultaneously to
finitely many middle flow lines proves the following monotonicity statement"). Lemma 7.1's landed forms
(`Lemma71PocketStatement`, `Lemma71PocketPinStatement`, `Lemma71TraceReferenceStatement`) describe the law of the
mapped pocket curve, not an ordering of two copies. A same-angle ordering of conditionally independent copies would
be a new theorem (it is equivalent to the determination being proved), so it is not taken as an input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Prop73Det

/-! ### The named inputs -/

/-- **Named input: the embedded reference of Lemmas 7.1–7.2** (specification §7.1, `source/spec/p193-240.md`
L576–L642, pp. 223–227; Proposition 7.3's proof, p. 242: "The embedded construction has produced one pair in which the
field determines the curve, with the canonical retained-range kernels"). For `0 < κ < 4` and seed weights
`ρ^L, ρ^R > −2` there is one coupling of the two-seed word `SLE_κ(ρ^L; ρ^R)` (marks at `0⁻`, `0⁺`) with the field,
satisfying the original optional hull specification of Theorem 1.1 (Lemma 7.1: "The joint pair with `h_ψ` has the
original coupling specification"), whose killed driving history is a Borel function of the field (Lemma 7.2: "In the
embedded coupling constructed above, `h_ψ` almost surely determines `η_ψ`"; the driving history is the Loewner
transform of the capacity-parametrized curve). The remark after Lemma 7.2 (p. 227: "As `θ₁ < 0 < θ₂` vary, (CPF2)
ranges over every pair `ρ^L, ρ^R > −2` […] The embedded construction therefore covers every admissible two-seed
pair") gives every pair. This is the form of the reference used for Theorem R.7 at `κ > 4`
(`R7.R7ReferenceStatement`, without its trace clause, which `Sec7.Prop73TraceStatement` carries here). -/
def Prop73ReferenceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ

/-- **Named input: Aux. lemma 50 for the boundary-hitting two-seed words, `0 < κ < 4`** (covariance exhaustion across
a continuous trace, `source/spec/p193-240.md` L816ff., pp. 236–241, "with any parameter `κ > 0`"; used through Aux.
lemma 51, p. 242, in Proposition 7.3's proof, p. 243: "The covariance-exhaustion argument identifies an explicit
common distributional mean and the full raw-range Green covariance as functions of that recorded history, so this
equality includes every component kernel"). For `0 < κ < 4` and seed weights `ρ^L, ρ^R > −2` of which at least one is
below `κ/2 − 2` (the curve hits the real line and cuts off pockets), there is one Borel kernel `Ψ` which is the
conditional characteristic function of the whole field given the killed driving history in every two-seed coupling
with the original optional hull specification whose driver has a continuous trace. This is the `κ < 4` twin of
`R7.R7FieldKernelStatement` (Theorem R.7's input at `κ > 4`). For `ρ^L, ρ^R ≥ κ/2 − 2` it is not needed (Aux. lemma
23, `Sec4.isOptionalHullLawUnique_of_admissible`). -/
def Prop73FieldKernelStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ rL rR : ℝ, -2 < rL → -2 < rR → (rL < κ / 2 - 2 ∨ rR < κ / 2 - 2) →
    ∃ Ψ : LawUnique.HistorySpace 1 1 → LQGMetric.TestOn upperHalfPlaneOpens → ℂ,
      (∀ φ, Measurable fun x => Ψ x φ) ∧ R7.TwoSeedTraceFieldKernel.{u} κ rL rR Ψ

/-! ### The two regimes -/

variable {κ rL rR : ℝ}

/-- The finite-time continuity of the two-seed evolutions (`R7.TwoSeedHasTraces`) from the trace part of
Proposition 7.3. -/
theorem twoSeedHasTraces_of_prop73Trace (h73t : Sec7.Prop73TraceStatement.{u}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : -2 < rL) (hR : -2 < rR) : R7.TwoSeedHasTraces.{u} κ rL rR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hc := h73t κ hκ hκ4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) (fun _ => rfl) (fun _ => rfl)
    (fun _ => hL) (fun _ => hR) P 𝓕 W VL VR B ζ hE
  filter_upwards [hc] with ω hω
  obtain ⟨η, hη, -⟩ := hω
  exact ⟨η, hη⟩

/-- **Proposition 7.3's determination, non-boundary-intersecting pairs** (`ρ^L, ρ^R ≥ κ/2 − 2`): one reference
coupling with a field-determined killed driving history makes every coupling field-determined. The identification of
the joint law is Aux. lemma 23 for words with admissible partial sums (`Sec4.isOptionalHullLawUnique_of_admissible`,
proved: the trace is simple, in `ℍ` at positive times and thin). -/
theorem hasFieldDeterminedHistories_twoSeed_of_admissible (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : κ / 2 - 2 ≤ rL) (hR : κ / 2 - 2 ≤ rR)
    (href : ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    LP.HasFieldDeterminedHistories.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) :=
  Sec4.hasFieldDeterminedHistories_of_admissible_of_reference.{u, u} hκ hκ4.le LP.isOrderedForceWord_twoSeed
    (WangWu.Theorem18.hasAdmissiblePartialSums_twoSeed hL hR) href

/-- **Proposition 7.3's determination, boundary-hitting pairs**: one reference coupling with a field-determined
killed driving history, the finite-time continuity of the two-seed evolutions and a common field kernel (Aux. lemma 50)
make every coupling field-determined (Aux. lemma 51 and the transfer of the graph; the argument of Theorem R.7,
`R7.hasFieldDeterminedHistories_twoSeed_of_reference`, which holds for every `κ > 0`). -/
theorem hasFieldDeterminedHistories_twoSeed_of_kernel (hκ : 0 < κ)
    {Ψ : LawUnique.HistorySpace 1 1 → LQGMetric.TestOn upperHalfPlaneOpens → ℂ}
    (hΨ : ∀ φ, Measurable fun x => Ψ x φ) (htr : R7.TwoSeedHasTraces.{u} κ rL rR)
    (hK : R7.TwoSeedTraceFieldKernel.{u} κ rL rR Ψ)
    (href : ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    LP.HasFieldDeterminedHistories.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) :=
  R7.hasFieldDeterminedHistories_twoSeed_of_reference.{u, u} hκ hΨ htr htr hK hK href

/-! ### Proposition 7.3, determination -/

/-- **Proposition 7.3, determination** (`Determination.Prop73DeterminationStatement`, the named input of LOCEXT's
Lemma 7.5 and of the Theorem 1.2 wiring), from the embedded reference of Lemmas 7.1–7.2
(`Prop73ReferenceStatement`), Aux. lemma 50 for the boundary-hitting pairs (`Prop73FieldKernelStatement`) and the trace
part of Proposition 7.3 (`Sec7.Prop73TraceStatement`, used only for the boundary-hitting pairs). -/
theorem prop73DeterminationStatement_of_reference (h73t : Sec7.Prop73TraceStatement.{u})
    (href : Prop73ReferenceStatement.{u}) (hK : Prop73FieldKernelStatement.{u}) :
    Determination.Prop73DeterminationStatement.{u} := by
  intro κ hκ hκ4 rL rR hL hR
  by_cases hadm : κ / 2 - 2 ≤ rL ∧ κ / 2 - 2 ≤ rR
  · exact hasFieldDeterminedHistories_twoSeed_of_admissible hκ hκ4 hadm.1 hadm.2 (href κ hκ hκ4 rL rR hL hR)
  · have hlow : rL < κ / 2 - 2 ∨ rR < κ / 2 - 2 := by
      rw [not_and_or, not_le, not_le] at hadm
      exact hadm
    obtain ⟨Ψ, hΨ, hKΨ⟩ := hK κ hκ hκ4 rL rR hL hR hlow
    exact hasFieldDeterminedHistories_twoSeed_of_kernel hκ hΨ
      (twoSeedHasTraces_of_prop73Trace h73t hκ hκ4 hL hR) hKΨ (href κ hκ hκ4 rL rR hL hR)

/-! ### Lemma 7.5 (both forms) from these inputs -/

/-- **Lemma 7.5 per coupling** (`LP.Lemma75DeterminationStatement`, the input of LP11) from the inputs of Proposition
7.3 and LOCEXT's inputs of Aux. lemmas 53–55 (`LocalExt.lemma75DeterminationStatement_of_restartSeedCoupling`). -/
theorem lemma75DeterminationStatement_of_reference (h73t : Sec7.Prop73TraceStatement.{u})
    (href : Prop73ReferenceStatement.{u}) (hK : Prop73FieldKernelStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.StoppedSeedExtensionStatement.{u} κ)
    (hrs : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartSeedCouplingStatement.{u} κ) :
    LP.Lemma75DeterminationStatement.{u} :=
  LocalExt.lemma75DeterminationStatement_of_restartSeedCoupling
    (prop73DeterminationStatement_of_reference h73t href hK) h73t hext hrs

/-- **Lemma 7.5, universal form** (`Theorem15.Lemma75Statement`, the input of Theorem 1.5) from the inputs of
Proposition 7.3 and LOCEXT's inputs of Aux. lemmas 53–55. -/
theorem lemma75Statement_of_reference (h73t : Sec7.Prop73TraceStatement.{u})
    (href : Prop73ReferenceStatement.{u}) (hK : Prop73FieldKernelStatement.{u})
    (hext : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.StoppedSeedExtensionStatement.{u} κ)
    (hrs : ∀ κ : ℝ, 0 < κ → κ < 4 → LocalExt.RestartSeedCouplingStatement.{u} κ) :
    Theorem15.Lemma75Statement.{u} :=
  Lemma75Bridge.lemma75Statement_of_lemma75DeterminationStatement
    (lemma75DeterminationStatement_of_reference h73t href hK hext hrs)

end Prop73Det

end InteractingSLE
