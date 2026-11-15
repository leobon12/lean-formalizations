/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Sec7.TwoForceMainLemma75

/-!
# Corollary LP7: complete finite-force driving determination for `k > 4`

Packet PROVE-R17. Supplement §6.6, Corollary LP7 (`source/spec/p481-528.md` L163–L172, pp. 487–488):
"Fix `k > 4`. Theorem R.7 and Lemma 7.25 supply a universally determined canonical two-seed coupling
for every pair `r_L, r_R > −2`. For every finite force word, the complete integrated driving and
force-coordinate history up to its continuation threshold is a measurable function of the coupling
field." Its proof: "The mixed and outer construction covers the pairs with `max(r_L, r_R) ≥ d`; Lemma
7.25 covers both strict inequalities `r_L, r_R < d`. Their buffered reference transfers and
full-joint-law graph arguments therefore give all admissible two-seed graphs. Apply Aux. 52–55: their
measurable maximal extension, own-history restart, and whole-field Cameron–Martin recoding arguments
are parameter-free […]. The finite-coordinate endpoint extension is Aux. lemma 3."

This file formalizes that proof: the case split of the two-seed pairs between Theorem R.7 and Lemma
7.25, and Aux. lemma 52 with the finite-coordinate endpoint extension (PROVE-SEC7-A2's
`Sec7.lem75_lifetime_of_restart` and `Sec7.lem75_killedState_of_restart`, reused, with PROVE-LP's
bridge `isFieldDeterminedHistory_of_isAEDeterminedBy`). The named inputs are

* `R7DeterminationStatement` (Theorem R.7, p. 477: "every coupling with the original optional hull
  specification has the same full field–driver joint law and determining graph"),
* `Lemma725DeterminationStatement` (Lemma 7.25, p. 413, its determination assertion),
* `TheoremR7TraceStatement`, `Lemma725TraceStatement` (`LPAssembly.lean`; the trace half of the
  two-seed input of Aux. lemma 55),
* `Aux55RestartStatement` (Aux. lemmas 53–55, pp. 244–247: the local restart (LG1) of Aux. lemma 52,
  from the two-seed input).

The main result is `lp7DeterminationStatement_of_inputs : … → LP7DeterminationStatement`, the named
input of LP11's assembly. **LP7 is not proved outright**: its five inputs remain (see
`planning/handoffs/PROVE-R17.md`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.LP

/-- **The local restart property (LG1) of Aux. lemma 52** for the field `h` of a coupling, in a
filtration `𝓖`: every bounded stopped history (stopped at a `𝓖`-stopping time `τ ≤ ζ ∧ N`)
determined by `h` extends to a strictly longer one, unless it already reached `ζ ∧ N` (PROVE-SEC7-A2's
hypothesis `hloc` of `Sec7.lem75_killedState_of_restart`, verbatim). -/
def HasFieldLocalRestarts {Ω : Type u} {mΩ : MeasurableSpace Ω} {nL nR : ℕ} (P : Measure Ω)
    (𝓖 : Filtration ℝ≥0 mΩ) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ (τ : Ω → WithTop ℝ≥0) (N : ℝ≥0), IsStoppingTime 𝓖 τ →
    (∀ ω, τ ω ≤ min (ζ ω : WithTop ℝ≥0) N) →
    Sec7.IsAEDeterminedBy P h (Sec7.stoppedHistory (Sec7.completedState W VL VR ζ) τ) →
    ∃ σ : Ω → WithTop ℝ≥0, IsStoppingTime 𝓖 σ ∧ (∀ ω, σ ω ≤ min (ζ ω : WithTop ℝ≥0) N) ∧
      (∀ᵐ ω ∂P, τ ω ≤ σ ω ∧ (τ ω < min (ζ ω : WithTop ℝ≥0) N → τ ω < σ ω)) ∧
      Sec7.IsAEDeterminedBy P h (Sec7.stoppedHistory (Sec7.completedState W VL VR ζ) σ)

/-- **The two-seed input of Aux. lemma 55** at `κ` ("for the two total weights `r_−, r_+ > −2` at
the seed […], every coupling with the original hull specification has a continuous trace determined by
its field", p. 244), for every admissible pair: the driving history of every two-seed coupling is
field-determined (hence its trace, by LP11's reconstruction `LPTrace.lean`), and every two-seed
evolution has a continuous generating trace. -/
def TwoSeedGraphInput (κ : ℝ) : Prop :=
  ∀ rL rR : ℝ, -2 < rL → -2 < rR →
    HasFieldDeterminedHistories.{u} κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) ∧
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η

/-- **Named input: Aux. lemmas 53–55** (specification §7.1, `source/spec/p241-288.md` L96–L131 and
L245, pp. 244–247: "Applying Aux. lemma 55 conditionally and using its countable reference family
produces a strictly longer own-filtration stopped driving history determined by `h`"), parameter-free:
under the two-seed input, every coupling of an ordered force word satisfying the optional hull
specification has the local restart property in its own driving filtration. (Aux. lemma 55 assumes
an admissible seed; for an inadmissible seed `ζ = 0` a.s. and the restart property is immediate.) -/
def Aux55RestartStatement (κ : ℝ) : Prop :=
  TwoSeedGraphInput.{u} κ →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      IsOrderedForceWord xL xR →
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
        (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
        (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
        IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
        ∀ hX : IsMeasurableKilledDriving W VL VR ζ,
          HasFieldLocalRestarts P (drivingFiltration P hX) h W VL VR ζ

/-- **Named input: the determination assertion of Theorem R.7** (supplement §5.7, p. 477: "every
coupling with the original optional hull specification has the same full field–driver joint law and
determining graph"), for `k > 4`, `r_L, r_R > −2`, `max(r_L, r_R) ≥ d = k/2 − 4`. -/
def R7DeterminationStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
    HasFieldDeterminedHistories.{u} κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR)

/-- **Named input: the determination assertion of Lemma 7.25** (p. 413, as used by LP7: "Lemma 7.25
covers both strict inequalities `r_L, r_R < d`"), for `k > 4`. -/
def Lemma725DeterminationStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
    HasFieldDeterminedHistories.{u} κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR)

/-- **LP7's first step**: Theorem R.7 and Lemma 7.25 supply the two-seed input of Aux. lemma 55 for
every admissible pair (`max(r_L, r_R) ≥ d` by R.7, both `< d` by Lemma 7.25). -/
theorem twoSeedGraphInput_of_inputs (hR7d : R7DeterminationStatement.{u})
    (hR7t : TheoremR7TraceStatement.{u}) (h725d : Lemma725DeterminationStatement.{u})
    (h725t : Lemma725TraceStatement.{u}) {κ : ℝ} (hκ : 4 < κ) : TwoSeedGraphInput.{u} κ := by
  intro rL rR hL hR
  rcases le_or_gt (κ / 2 - 4) (max rL rR) with hmax | hmax
  · refine ⟨hR7d κ hκ rL rR hL hR hmax, fun P _ 𝓕 W VL VR B ζ hE => ?_⟩
    filter_upwards [hR7t κ hκ rL rR hL hR hmax P 𝓕 W VL VR B ζ hE] with ω hω
    obtain ⟨η, hη, -⟩ := hω
    exact ⟨η, hη⟩
  · have h1 : rL < κ / 2 - 4 := lt_of_le_of_lt (le_max_left _ _) hmax
    have h2 : rR < κ / 2 - 4 := lt_of_le_of_lt (le_max_right _ _) hmax
    exact ⟨h725d κ hκ rL rR hL h1 hR h2, h725t κ hκ rL rR hL h1 hR h2⟩

/-- **Aux. lemma 52 and the endpoint extension** (PROVE-SEC7-A2, reused): a coupling with the local
restart property in its own driving filtration has a field-determined killed driving history. -/
theorem isFieldDeterminedHistory_of_hasFieldLocalRestarts {κ : ℝ} (hκ : 0 < κ) {nL nR : ℕ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) {𝓖 : Filtration ℝ≥0 mΩ}
    (hloc : HasFieldLocalRestarts P 𝓖 h W VL VR ζ) : IsFieldDeterminedHistory P h W VL VR ζ :=
  isFieldDeterminedHistory_of_isAEDeterminedBy
    (Sec7.lem75_lifetime_of_restart hκ hcoup.1 hcoup.2.1 hloc) (0, xL, xR)
    (Sec7.lem75_killedState_of_restart hκ hcoup.1 hcoup.2.1 hloc (0, xL, xR))

/-- **Corollary LP7 (the named input `LP7DeterminationStatement` of LP11's assembly), from its
inputs**: for `k > 4`, Theorem R.7 and Lemma 7.25 (determination and finite-time traces of the
two-seed couplings) and Aux. lemmas 53–55 give field determination of the killed driving history of
every coupling of every ordered force word satisfying the optional hull specification. -/
theorem lp7DeterminationStatement_of_inputs (hR7d : R7DeterminationStatement.{u})
    (hR7t : TheoremR7TraceStatement.{u}) (h725d : Lemma725DeterminationStatement.{u})
    (h725t : Lemma725TraceStatement.{u}) (h55 : ∀ κ : ℝ, 4 < κ → Aux55RestartStatement.{u} κ) :
    LP7DeterminationStatement.{u} := by
  intro κ hκ nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hcoup
  obtain ⟨hX, -⟩ := hcoup.2.2.2
  exact isFieldDeterminedHistory_of_hasFieldLocalRestarts (by linarith) hcoup
    (h55 κ hκ (twoSeedGraphInput_of_inputs hR7d hR7t h725d h725t hκ) xL xR ρL ρR hF P 𝓕 W VL VR B
      ζ h hcoup hX)

end InteractingSLE.LP
