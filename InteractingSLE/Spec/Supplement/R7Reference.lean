/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPProbDetermination
import InteractingSLE.Spec.Coupling.LawUniqueKernel
import InteractingSLE.Spec.Sec7.TwoForceMain3Prop73
import InteractingSLE.Spec.Sec7.CounterflowProbTransfer
import InteractingSLE.Foundations.Loewner.TraceCodingTop
import InteractingSLE.Spec.Sec7.TraceCodingUse
import InteractingSLE.Spec.Sec7.DeterminationRestart

/-!
# Theorem R.7: the output interface of the mixed and outer two-seed references (`k > 4`)

Packet PROVE-R7. Supplement §5.7, Theorem R.7 and its proof (`source/spec/p433-480.md` L1051–L1070, pp. 477–478), in
the repaired form of ruling R41 (`source/external/AstraIG1/ig1_ztip_elimination.txt` §2, Theorem 2.1, lines 485–568:
"The revised R.7 has the same output interface as before").

> **Theorem R.7.** Fix `k > 4` and put `d = k/2 − 4`. For every pair `r_L, r_R > −2`, `max(r_L, r_R) ≥ d`, there is an
> actual non-boundary Jordan-pocket construction satisfying the canonical component reference predicate of Section 4,
> with precisely the two seed groups `(r_L, r_R)`, no other nonzero force group, and infinite relative capacity
> lifetime. […] In its entry-to-exit half-plane chart the relative trace is continuous on `[0, ∞)` and tends to
> infinity. Its full normalized field–path law is the canonical two-seed law and is concentrated on one Borel
> field–driver graph. **Consequently** the integrated `SLE_k(r_L; r_R)` driving law has this continuous transient
> trace, and every coupling with the original optional hull specification has the same full field–driver joint law
> and determining graph.

The two consequences are the forms LP7 and LP11 consume: `LP.TheoremR7TraceStatement` and
`LP.R7DeterminationStatement` (`LPAssembly.lean`, `LPProbDetermination.lean`). This file proves both from

* **the reference itself** (`R7ReferenceStatement`): one coupling of the two-seed word with the original optional hull
  specification, whose driver almost surely has a continuous generating trace on `[0, ∞)` tending to infinity, and
  whose killed driving history is a Borel function of its field. This is the output of the geometric construction of
  §§5.1–5.6 (Lemmas R.1–R.6 with the repairs of ruling R41) together with Aux. lemmas 119–125 and 131 and Theorem 2.4
  (see "What is not proved here");
* **Aux. lemma 50 for the two-seed word** (`R7FieldKernelStatement`): once finite-time continuity is known, every
  original two-seed coupling has the same conditional law of the whole field given its killed driving history (Aux.
  lemma 126's proof, p. 401: "At this stage finite-time continuity has already been proved from the driving marginal
  alone. Aux. lemma 50 therefore applies to every original two-seed coupling […] Its full conditional field kernel is
  the same function of the stopped history in all those couplings").

## The proof steps formalized here

1. **Infinite lifetime** ("Thus `L = ∞`, the killing rule disappears"): both seed weights exceed `−2`, so every
   integrated two-seed evolution has infinite lifetime (`Sec7.ae_lifetime_eq_top_twoSeed`, from the landed Jacobi
   diffusion `Sec7.jacobiDiffusionExistsStatement`). In this formalization the step needs no geometric input.
2. **The trace consequence** ("Consequently the integrated `SLE_k(r_L; r_R)` driving law has this continuous transient
   trace"): the reference evolution has a transient trace; the event is a measurable function of the driver
   (`Sec7.transientTraceCodingStatement`) and Theorem 2.2's two-seed uniqueness in law transfers it to every two-seed
   evolution (`Sec7.ae_transfer_of_coding`): `theoremR7TraceStatement_of_reference`.
3. **The joint law** ("every coupling with the original optional hull specification has the same full field–driver
   joint law"): Theorem 2.2's two-seed uniqueness of the killed driving law (`LawUnique.killedStateLawUnique_twoSeed`)
   and the common field kernel of Aux. lemma 50 give one joint law of field and history
   (`LawUnique.isOptionalHullLawUnique_of_hasOptionalHullFieldKernel`). For any `κ > 0` and seed pair, from finite-time
   continuity (`TwoSeedHasTraces`) and the kernel: `isOptionalHullLawUnique_twoSeed`; for the R.7 pairs, with the
   continuity of step 2: `isOptionalHullLawUnique_twoSeed_of_inputs`.
4. **The determining graph** ("and determining graph"; Aux. lemma 126's last paragraph, "Comparing with the dilated
   reference transfers its graph to every original coupling"; for this reference no dilation is needed, its lifetime
   being infinite): the reference graph transfers along the common joint law
   (`LawUnique.hasFieldDeterminedHistories_of_isOptionalHullLawUnique`). Generic form
   `hasFieldDeterminedHistories_twoSeed_of_reference` (also usable for the both-low pairs of Lemma 7.25); for R.7:
   `r7DeterminationStatement_of_inputs`.
5. **Into LP7** (Corollary LP7, p. 487): `lp7DeterminationStatement_of_r7` and `lp7DeterminationStatement_of_r7_localExtension`.

## What is not proved here

The reference (`R7ReferenceStatement`). Its proof is the random geometric construction of supplement §§5.1–5.6: the
complete non-boundary centered counterflow `η` coupled with `F = −h − πχ`, the extremal flow lines `β_R, β_L` and their
exterior sides, the outer and contained incoming arms of the chosen angles (`R7Angles.lean`), the selected Jordan pocket
`C`, its active charts `g_s`, the erased relative traversal and its continuous relative driver (R.3, R.4, the repaired
gap paragraphs: Propositions 1.5–1.6 of the repair note with the fixed-chart gate lemma, `R4Gaps.lean`), the all-stop
Gaussian kernels (R.5 with Aux. 27–29), the zero phase (R.6 with Aux. 122 and 131), the initial word (Aux. 119–121), the
SDE identification (Theorem 2.4) and the determining graph (Aux. 124–125). None of these random objects exists in Lean
(see `planning/handoffs/PROVE-R7.md`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u v w

namespace InteractingSLE

namespace R7

/-! ### Named inputs -/

/-- **The mixed and outer two-seed reference** (Theorem R.7, supplement p. 477, `source/spec/p433-480.md` L1052–L1056,
its constructive assertion; repaired proof: ruling R41, `ig1_ztip_elimination.txt` Theorem 2.1): for `k > 4`,
`r_L, r_R > −2` and `max(r_L, r_R) ≥ d = k/2 − 4` there is one coupling of the two-seed word `SLE_k(r_L; r_R)` (the
normalized field–path pair of the selected pocket: "Its full normalized field–path law is the canonical two-seed law")
which satisfies the original optional hull specification, whose driver almost surely has a continuous generating trace
on `[0, ∞)` tending to infinity ("In its entry-to-exit half-plane chart the relative trace is continuous on `[0, ∞)`
and tends to infinity"), and whose killed driving history is a Borel function of its field ("concentrated on one Borel
field–driver graph", Aux. lemmas 124–125). -/
def R7ReferenceStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.HasTransientGeneratingTrace P W ζ ∧ LP.IsFieldDeterminedHistory P h W VL VR ζ

/-- The field kernel `Ψ` of Aux. lemma 50 for the two-seed word: every coupling of `SLE_κ(r_L; r_R)` with the original
optional hull specification (on a probability space in the universe `u`) whose driver almost surely has a continuous
generating trace through its lifetime has the conditional characteristic functions
`E[e^{i(h, φ)} | σ(history)] = Ψ(history, φ)` of its whole field given its killed driving history. -/
def TwoSeedTraceFieldKernel (κ rL rR : ℝ)
    (Ψ : LawUnique.HistorySpace 1 1 → LQGMetric.TestOn upperHalfPlaneOpens → ℂ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h →
    (∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) →
    LawUnique.IsHistoryFieldKernel P h (LawUnique.killedHistory W VL VR ζ) Ψ

/-- **Named input: Aux. lemma 50 for the R.7 two-seed words** (specification p. 236; used in Aux. lemma 126's proof,
p. 401, "Aux. lemma 50 therefore applies to every original two-seed coupling […] Its full conditional field kernel is
the same function of the stopped history in all those couplings"; at the terminal history, as in
`LawUnique.HasOptionalHullFieldKernel`): for `k > 4` and the pairs of Theorem R.7 there is one Borel kernel `Ψ` which
is the field kernel of every two-seed coupling with a continuous trace, on probability spaces in the universes `u` and
`v`. -/
def R7FieldKernelStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
    ∃ Ψ : LawUnique.HistorySpace 1 1 → LQGMetric.TestOn upperHalfPlaneOpens → ℂ,
      (∀ φ, Measurable fun x => Ψ x φ) ∧ TwoSeedTraceFieldKernel.{u} κ rL rR Ψ ∧
        TwoSeedTraceFieldKernel.{v} κ rL rR Ψ

/-! ### Step 1: infinite lifetime -/

section Evolution

variable {κ rL rR : ℝ}

/-- **Infinite relative lifetime** (Theorem R.7's proof, p. 477: "Both seed weights exceed `−2`. […] This
contradiction excludes every finite `L`. Thus `L = ∞`, the killing rule disappears"): every integrated two-seed
evolution with weights `> −2` has infinite lifetime almost surely (Theorem 2.2's proof; `Sec7.ae_lifetime_eq_top_twoSeed`
with the landed Jacobi diffusion). -/
theorem ae_lifetime_eq_top (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ :=
  Sec7.ae_lifetime_eq_top_twoSeed (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hL hR
    Sec7.jacobiDiffusionExistsStatement hE

/-! ### Step 2: the trace consequence -/

/-- **Transfer of the transient trace from one reference evolution** (Theorem R.7, p. 477: "Consequently the
integrated `SLE_k(r_L; r_R)` driving law has this continuous transient trace"): if one integrated two-seed evolution
almost surely has a continuous generating trace on `[0, ∞)` tending to infinity, so has every integrated two-seed
evolution with the same weights. The event is a measurable function of the driver (`Sec7.transientTraceCodingStatement`)
and the driving law is unique (Theorem 2.2, `Sec7.ae_transfer_of_coding`). -/
theorem hasTransientGeneratingTrace_of_reference (hκ : 0 < κ) (hL : -2 < rL) (hR : -2 < rR)
    {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀} {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    {𝓕₀ : Filtration ℝ≥0 m₀} {W₀ : ℝ≥0 → Ω₀ → ℝ} {VL₀ VR₀ : Fin 1 → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ}
    {ζ₀ : Ω₀ → ℝ≥0∞}
    (hE₀ : IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀)
    (htr₀ : LP.HasTransientGeneratingTrace P₀ W₀ ζ₀)
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    LP.HasTransientGeneratingTrace P W ζ := by
  obtain ⟨G, hG, hGp⟩ := Sec7.transientTraceCodingStatement
  rw [Sec7.hasTransientGeneratingTrace_iff_of_top (ae_lifetime_eq_top hκ hL hR hE)]
  exact Sec7.ae_transfer_of_coding (ρL := fun _ => rL) (ρR := fun _ => rR) hκ hL hR
    Sec7.jacobiDiffusionExistsStatement hG hGp hE₀
    ((Sec7.hasTransientGeneratingTrace_iff_of_top (ae_lifetime_eq_top hκ hL hR hE₀)).1 htr₀) hE

end Evolution

/-- **Theorem R.7, the trace consequence** (`LP.TheoremR7TraceStatement`, the named input of LP5, LP7 and LP11): for
`k > 4`, `r_L, r_R > −2` and `max(r_L, r_R) ≥ d`, the two-seed word is complete: every integrated `SLE_k(r_L; r_R)`
evolution almost surely has a continuous generating trace on `[0, ∞)` tending to infinity. From the reference. -/
theorem theoremR7TraceStatement_of_reference (href : R7ReferenceStatement.{v}) :
    LP.TheoremR7TraceStatement.{u} := by
  intro κ hκ rL rR hL hR hmax Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨Ω₀, m₀, P₀, _, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, htr₀, -⟩ := href κ hκ rL rR hL hR hmax
  exact hasTransientGeneratingTrace_of_reference (by linarith) hL hR hC₀.1 htr₀ hE

/-- Every integrated two-seed evolution of a Theorem R.7 pair almost surely has a continuous generating trace through
its lifetime (the finite-time continuity that Aux. lemma 50 requires). -/
theorem ae_exists_isGeneratingTrace_of_reference (href : R7ReferenceStatement.{v}) {κ : ℝ} (hκ : 4 < κ)
    {rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR) (hmax : κ / 2 - 4 ≤ max rL rR) {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η := by
  filter_upwards [theoremR7TraceStatement_of_reference.{u, v} href κ hκ rL rR hL hR hmax P 𝓕 W VL VR B ζ hE]
    with ω hω
  obtain ⟨η, hη, -⟩ := hω
  exact ⟨η, hη⟩

/-! ### Steps 3–4: the joint law and the determining graph -/

section Generic

/-- Every integrated two-seed evolution `SLE_κ(r_L; r_R)` (on a probability space in the universe `u`) almost surely
has a continuous generating trace through its lifetime (the finite-time continuity that Aux. lemma 50 requires; the
second half of `LP.TwoSeedGraphInput`). -/
def TwoSeedHasTraces (κ rL rR : ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η

variable {κ rL rR : ℝ} {Ψ : LawUnique.HistorySpace 1 1 → LQGMetric.TestOn upperHalfPlaneOpens → ℂ}

/-- The common field kernel of Aux. lemma 50 holds for every two-seed coupling once every two-seed evolution has a
continuous trace. -/
theorem hasOptionalHullFieldKernel_twoSeed_of_traces (htr : TwoSeedHasTraces.{u} κ rL rR)
    (hK : TwoSeedTraceFieldKernel.{u} κ rL rR Ψ) :
    LawUnique.HasOptionalHullFieldKernel.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) Ψ := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ h hC
  exact hK P 𝓕 W VL VR B ζ h hC (htr P 𝓕 W VL VR B ζ hC.1)

/-- **The common joint law of the two-seed couplings** (Aux. lemma 126, p. 401: "Aux. lemma 50 therefore applies to
every original two-seed coupling […] Together with integrated driving uniqueness this identifies the full joint law of
the whole field and the stopped history"), for any `κ > 0` and seed weights: Theorem 2.2's two-seed uniqueness
(`LawUnique.killedStateLawUnique_twoSeed`), finite-time continuity and the common kernel of Aux. lemma 50 give one
joint law of field and killed driving history. -/
theorem isOptionalHullLawUnique_twoSeed (hκ : 0 < κ) (hΨ : ∀ φ, Measurable fun x => Ψ x φ)
    (htr₁ : TwoSeedHasTraces.{u} κ rL rR) (htr₂ : TwoSeedHasTraces.{v} κ rL rR)
    (hK₁ : TwoSeedTraceFieldKernel.{u} κ rL rR Ψ) (hK₂ : TwoSeedTraceFieldKernel.{v} κ rL rR Ψ) :
    LawUnique.IsOptionalHullLawUnique.{u, v} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) :=
  LawUnique.isOptionalHullLawUnique_of_hasOptionalHullFieldKernel hΨ
    (LawUnique.killedStateLawUnique_twoSeed hκ _ _ (fun _ => rfl) fun _ => rfl)
    (hasOptionalHullFieldKernel_twoSeed_of_traces htr₁ hK₁) (hasOptionalHullFieldKernel_twoSeed_of_traces htr₂ hK₂)

/-- **The determining graph transfers from one two-seed reference** (Aux. lemma 126, p. 401: "Comparing with the
dilated reference transfers its graph to every original coupling"), for a reference coupling (universe `v`) with
infinite lifetime, so that no dilation is needed: under finite-time continuity and the common kernel of Aux. lemma 50,
every two-seed coupling (universe `u`) has a field-determined killed driving history. -/
theorem hasFieldDeterminedHistories_twoSeed_of_reference (hκ : 0 < κ) (hΨ : ∀ φ, Measurable fun x => Ψ x φ)
    (htr₁ : TwoSeedHasTraces.{v} κ rL rR) (htr₂ : TwoSeedHasTraces.{u} κ rL rR)
    (hK₁ : TwoSeedTraceFieldKernel.{v} κ rL rR Ψ) (hK₂ : TwoSeedTraceFieldKernel.{u} κ rL rR Ψ)
    (href : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ h ∧
        LP.IsFieldDeterminedHistory P h W VL VR ζ) :
    LP.HasFieldDeterminedHistories.{u} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) :=
  LawUnique.hasFieldDeterminedHistories_of_isOptionalHullLawUnique
    (isOptionalHullLawUnique_twoSeed hκ hΨ htr₁ htr₂ hK₁ hK₂) href

end Generic

/-- The trace consequence in the form `TwoSeedHasTraces`, for the Theorem R.7 pairs. -/
theorem twoSeedHasTraces_of_reference (href : R7ReferenceStatement.{w}) {κ : ℝ} (hκ : 4 < κ) {rL rR : ℝ}
    (hL : -2 < rL) (hR : -2 < rR) (hmax : κ / 2 - 4 ≤ max rL rR) : TwoSeedHasTraces.{u} κ rL rR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact ae_exists_isGeneratingTrace_of_reference href hκ hL hR hmax hE

/-- **The common joint law for the Theorem R.7 pairs** (Theorem R.7, p. 477: "every coupling with the original
optional hull specification has the same full field–driver joint law"): `isOptionalHullLawUnique_twoSeed` with the
continuity supplied by the trace consequence. -/
theorem isOptionalHullLawUnique_twoSeed_of_inputs (href : R7ReferenceStatement.{w})
    (hK : R7FieldKernelStatement.{u, v}) {κ : ℝ} (hκ : 4 < κ) {rL rR : ℝ} (hL : -2 < rL) (hR : -2 < rR)
    (hmax : κ / 2 - 4 ≤ max rL rR) :
    LawUnique.IsOptionalHullLawUnique.{u, v} κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) := by
  obtain ⟨Ψ, hΨ, hK₁, hK₂⟩ := hK κ hκ rL rR hL hR hmax
  exact isOptionalHullLawUnique_twoSeed (by linarith) hΨ (twoSeedHasTraces_of_reference href hκ hL hR hmax)
    (twoSeedHasTraces_of_reference href hκ hL hR hmax) hK₁ hK₂

/-- **Theorem R.7, the determination consequence** (`LP.R7DeterminationStatement`, the named input of LP7; p. 477:
"every coupling with the original optional hull specification has the same full field–driver joint law and determining
graph"): for `k > 4`, `r_L, r_R > −2` and `max(r_L, r_R) ≥ d`, the killed driving history of every two-seed coupling
with the original optional hull specification is a Borel function of its field. The reference graph transfers along the
common joint law (`hasFieldDeterminedHistories_twoSeed_of_reference`). -/
theorem r7DeterminationStatement_of_inputs (href : R7ReferenceStatement.{v}) (hK : R7FieldKernelStatement.{v, u}) :
    LP.R7DeterminationStatement.{u} := by
  intro κ hκ rL rR hL hR hmax
  obtain ⟨Ψ, hΨ, hK₁, hK₂⟩ := hK κ hκ rL rR hL hR hmax
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, -, hdet₀⟩ := href κ hκ rL rR hL hR hmax
  exact hasFieldDeterminedHistories_twoSeed_of_reference (by linarith) hΨ
    (twoSeedHasTraces_of_reference href hκ hL hR hmax) (twoSeedHasTraces_of_reference href hκ hL hR hmax) hK₁ hK₂
    ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, h₀, hC₀, hdet₀⟩

/-! ### Step 5: into Corollary LP7 -/

/-- **Corollary LP7 from Theorem R.7's inputs** (`LP.lp7DeterminationStatement_of_inputs` with both R.7 inputs
discharged by the reference and Aux. lemma 50). -/
theorem lp7DeterminationStatement_of_r7 (href : R7ReferenceStatement.{v}) (hK : R7FieldKernelStatement.{v, u})
    (h725d : LP.Lemma725DeterminationStatement.{u}) (h725t : LP.Lemma725TraceStatement.{u})
    (h55 : ∀ κ : ℝ, 4 < κ → LP.Aux55RestartStatement.{u} κ) : LP.LP7DeterminationStatement.{u} :=
  LP.lp7DeterminationStatement_of_inputs (r7DeterminationStatement_of_inputs href hK)
    (theoremR7TraceStatement_of_reference href) h725d h725t h55

/-- **Corollary LP7 from Theorem R.7's inputs and the local extensions of Aux. lemmas 53–55**
(`Determination.lp7DeterminationStatement_of_localExtension` with both R.7 inputs discharged). -/
theorem lp7DeterminationStatement_of_r7_localExtension (href : R7ReferenceStatement.{v})
    (hK : R7FieldKernelStatement.{v, u}) (h725d : LP.Lemma725DeterminationStatement.{u})
    (h725t : LP.Lemma725TraceStatement.{u})
    (hext : ∀ κ : ℝ, 4 < κ → Determination.LocalExtensionStatement.{u} κ) : LP.LP7DeterminationStatement.{u} :=
  Determination.lp7DeterminationStatement_of_localExtension (r7DeterminationStatement_of_inputs href hK)
    (theoremR7TraceStatement_of_reference href) h725d h725t hext

end R7

end InteractingSLE
