import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Frozen.Spec.IsOptionalHullCoupling
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution
import InteractingSLE.Frozen.Spec.ForceWord_ThresholdCondition
import InteractingSLE.Frozen.Spec.IsOrderedForceWord
import InteractingSLE.Spec.Sec7.TwoForceRestart

/-!
# Corollary LP11: Theorems 1.2–1.3 for every parameter, assembled from named inputs

Packet PROVE-LP (specification supplement §6.7, Corollary LP11, `source/spec/p481-528.md` L180–L215, pp. 488–489;
graph nodes `SPEC.id-LP11`, `SPEC.id-LP11#kappa-lt-4`, `SPEC.id-LP11#kappa-gt-4`, `SPEC.id-LP11#field-to-trace`).

The frozen Theorems 1.2 (`exists_measurable_lifetime_trace_eq_comp_field`) and 1.3
(`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`) are proved here **with exactly their frozen conclusions**,
modulo named inputs that are not yet in Lean. Everything else is proved:

* **Field to trace** (`exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory`): if the killed
  driving history `(ζ, W, V)` of a coupling is a Borel function of the field up to a null set
  (`IsFieldDeterminedHistory`), then so is `(ζ, t ↦ η(t ∧ ζ))` for every continuous generating trace `η` — LP11's
  "composition with the measurable field-to-driving map", through the deterministic reconstruction
  `LP.drivingTrace` (`LPTrace.lean`). No continuity theorem is used: the frozen Theorem 1.2 quantifies over the
  generating traces that exist.
* **The seed** (`IsIntegratedSLEEvolution.ae_eq_zero_of_thresholdCondition`): an inadmissible initial seed gives
  `T_* = 0`, directly from the maximal-lifetime reading of the integrated path.
* **The trace part of Theorem 1.3 per word** (`IsCompleteForceWord`) and the two-seed inputs of LP10
  (`isCompleteForceWord_twoSeed`: Theorem R.7 for `max(r_L, r_R) ≥ d`, Lemma 7.25 and LP4 for the strict both-low
  rectangle; LP11 proof p. 488 and "Two-seed inputs to the induction", p. 487).
* **The parameter split** of LP11's proof: `0 < κ < 4` (the revised §7.3 induction, Lemma 7.5 with Aux. 52–55),
  `κ = 4` (Wang–Wu, ruling R31: the Lean-preprocessed document's Theorems 1.7–1.8), `κ > 4` (LP10 with the two-seed
  inputs, LP7).

## The named inputs (each a `…Statement : Prop`; none is assumed anywhere else)

| Input | Source |
|---|---|
| `RevisedInductionLtFourStatement` | §7.3 "Revised induction for Theorem 1.3, `0 < κ < 4`", pp. 378–380 (LP11 proof, p. 488) |
| `Lemma75DeterminationStatement` | Lemma 7.5 (p. 252) with Aux. 52–55 (pp. 244–247), as used in LP11's proof (p. 488) |
| `WWTheorem17Statement` | Wang–Wu document (R31), Theorem 1.7 (= WW 1.1.2), on the frozen carriers |
| `WWTheorem18Statement` | Wang–Wu document (R31), Theorem 1.8 (= WW 1.1.3), on the frozen carriers |
| `LP7DeterminationStatement` | Corollary LP7, p. 487 (its determination assertion) |
| `LP10Statement` | Theorem LP10, p. 486 (its independent inputs Aux. 99 and Aux. 108–111 included) |
| `TheoremR7TraceStatement` | Theorem R.7, p. 477 (its trace consequence) |
| `Lemma725TraceStatement` | Lemma 7.25, p. 413 (finite-time continuity of the two-seed law) |
| `LP4Statement` | Proposition LP4, p. 482 |

The Wang–Wu inputs are stated over the frozen ordered force word, the carrier PROVE-WW-A uses for the document's
Definition 1.2. Its literal list form has distinct positions on each side (`IsDistinctForceWord`); the amalgamation of
coincident marks reduces the trace statement to that form (`CoincidentMarksTraceStatement`, **proved** in
`LPAmalgamate.lean`: `wwTheorem18Statement_of_distinct`). The determination form of the reduction
(`CoincidentMarksDeterminationStatement`) is stated but not proved and not used.

**Coupling notion at `κ = 4`.** The frozen Theorem 1.2 quantifies over couplings satisfying the optional hull
specification of Theorem 1.1 (`IsOptionalHullCoupling`), so `WWTheorem17Statement` asks for determination for those
couplings. The Wang–Wu document proves it for its Theorem 1.6 coupling and for couplings satisfying its Definition 1.5
(the full ambient-field kernel, `WangWu.IsFullLevelLineCoupling`); whoever discharges `WWTheorem17Statement` must
either show that the optional hull specification implies Definition 1.5's laws or run Theorem 4.25's argument from the
optional hull laws.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LP

/-! ### Field determination of the driving history implies field determination of the trace -/

/-- The killed driving history `(ζ, W, V^{·,L}, V^{·,R})` of a coupling with field `h` is a Borel function of the
field, up to a `P`-null set: there is a measurable `Ψ` on the distribution space (product σ-algebras on paths) with,
almost surely, `Ψ(h)` equal to the lifetime and to the driving and force coordinates at every time before the
lifetime ("the complete integrated driving and force-coordinate history up to its continuation threshold is a
measurable function of the coupling field", Corollary LP7, p. 487). -/
def IsFieldDeterminedHistory {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ} (P : Measure Ω)
    (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  ∃ Ψ : LQGMetric.DistOn upperHalfPlaneOpens →
      ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ),
    Measurable Ψ ∧ ∀ᵐ ω ∂P, (Ψ (h ω)).1 = ζ ω ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω →
      (Ψ (h ω)).2.1 t = W t ω ∧ (∀ i, (Ψ (h ω)).2.2.1 i t = VL i t ω) ∧
        ∀ i, (Ψ (h ω)).2.2.2 i t = VR i t ω

/-- **Bridge from the `Sec7` form of determination** (PROVE-SEC7-A2, `Sec7.lem75_lifetime_of_restart` and
`Sec7.lem75_killedState_of_restart`): if the lifetime and the killed driving state path
`t ↦ (W_t, V^L_t, V^R_t) 1_{t < ζ}` (a fixed value `c` from `ζ` on) are almost surely Borel functions of the field,
then the killed driving history is field-determined in the sense of `IsFieldDeterminedHistory`. -/
theorem isFieldDeterminedHistory_of_isAEDeterminedBy {Ω : Type u} [MeasurableSpace Ω] {nL nR : ℕ}
    {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hζ : Sec7.IsAEDeterminedBy P h ζ) (c : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))
    (hX : Sec7.IsAEDeterminedBy P h fun ω (t : ℝ≥0) =>
      if (t : ℝ≥0∞) < ζ ω then (W t ω, (fun i => VL i t ω), fun i => VR i t ω) else c) :
    IsFieldDeterminedHistory P h W VL VR ζ := by
  obtain ⟨g₁, hg₁, h₁⟩ := hζ
  obtain ⟨g₂, hg₂, h₂⟩ := hX
  have hc : ∀ t, Measurable fun d => g₂ d t := fun t => (measurable_pi_apply t).comp hg₂
  refine ⟨fun d => (g₁ d, fun t => (g₂ d t).1, fun i t => (g₂ d t).2.1 i, fun i t => (g₂ d t).2.2 i),
    hg₁.prodMk ((measurable_pi_iff.2 fun t => measurable_fst.comp (hc t)).prodMk
      ((measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun t =>
        (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (hc t)))).prodMk
      (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun t =>
        (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp (hc t)))))), ?_⟩
  filter_upwards [h₁, h₂] with ω e1 e2
  refine ⟨e1.symm, fun t ht => ?_⟩
  have e := congrFun e2 t
  rw [ite_eq_left_of_eq_true _ _ (eq_true ht)] at e
  simp only [← e, implies_true, and_self]

/-- **LP11, field to trace.** For a coupling satisfying the optional hull specification of Theorem 1.1 whose killed
driving history is a Borel function of the field, the lifetime and the entire capacity-parametrized trace
(frozen after a finite lifetime) are a Borel function of the field: the conclusion of the frozen Theorem 1.2. -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory {κ : ℝ}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hdet : IsFieldDeterminedHistory P h W VL VR ζ) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal := by
  obtain ⟨Ψ, hΨm, hΨ⟩ := hdet
  refine ⟨fun d => drivingTrace ((Ψ d).1, (Ψ d).2.1), ?_, ?_⟩
  · exact measurable_drivingTrace.comp
      ((measurable_fst.comp hΨm).prodMk (measurable_fst.comp (measurable_snd.comp hΨm)))
  filter_upwards [hΨ, hcoup.1.2.2.2.2] with ω hω hpath
  obtain ⟨hζ, hW⟩ := hω
  obtain ⟨hw0, -, -, hcw, -⟩ := hpath
  refine ⟨by simp [drivingTrace, hζ], fun η hη t => ?_⟩
  rw [hζ, drivingTrace_eq hη hcw hw0 fun s hs => (hW s hs).1]

/-! ### The inadmissible seed -/

/-- **An inadmissible seed gives `T_* = 0`** (Theorem 1.3, first assertion; LP11, p. 488): if the threshold
condition holds at the seed, the lifetime of an integrated evolution is `0` almost surely (the threshold fails before
the lifetime, in particular at time `0`). -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.ae_eq_zero_of_thresholdCondition {a : ℝ}
    {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0 := by
  filter_upwards [hE.2.2.2.2] with ω hpath hthr
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnt, -⟩ := hpath
  by_contra hne
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    rw [ENNReal.coe_zero]
    exact pos_iff_ne_zero.2 hne
  apply hnt 0 h0
  have hL : (fun i => VL i 0 ω) = xL := funext hvL0
  have hR : (fun i => VR i 0 ω) = xR := funext hvR0
  rw [hw0, hL, hR]
  exact hthr

/-! ### The trace part of Theorem 1.3 for one force word -/

/-- Almost surely there is a continuous generating trace of the Loewner chain driven by `W` on `[0, ζ]` (on every
finite interval when `ζ = ∞`), and it tends to infinity on `{ζ = ∞}`. -/
def HasTransientGeneratingTrace {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (W : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
    (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)

/-- **The complete theorem for a force word** (the "full continuity and transience assertion" of LP10, LP11 and
§7.3): every integrated `SLE_a(ρ)` evolution of the word, on any probability space, almost surely has a continuous
generating trace up to and including a finite continuation threshold, which tends to infinity on infinite
lifetime. -/
def IsCompleteForceWord (a : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ → HasTransientGeneratingTrace P W ζ

/-- The conclusion of the frozen Theorem 1.3 for an evolution of a complete force word. -/
theorem ae_exists_isGeneratingTrace_of_isCompleteForceWord {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hc : IsCompleteForceWord.{u} a xL xR ρL ρR)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  filter_upwards [hE.ae_eq_zero_of_thresholdCondition, hc P 𝓕 W VL VR B ζ hE] with ω h1 h2
  exact ⟨h1, h2⟩

/-- Every coupling of the force word satisfying the optional hull specification of Theorem 1.1 has a field-determined
killed driving history. -/
def HasFieldDeterminedHistories (κ : ℝ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h → IsFieldDeterminedHistory P h W VL VR ζ

/-- The force data of the Wang–Wu document's Definition 1.2 (ruling R31): an ordered force word whose positions are
distinct on each side, `x_{ℓ,L} < ⋯ < x_{1,L} ≤ 0 ≤ x_{1,R} < ⋯ < x_{r,R}` (the Lean index `0` is the source index
`1`). -/
def IsDistinctForceWord {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) : Prop :=
  IsOrderedForceWord xL xR ∧ StrictAnti xL ∧ StrictMono xR

/-- The two-seed force word `SLE(r_L; r_R)`: one left mark at `0⁻` of weight `r_L` and one right mark at `0⁺` of
weight `r_R`. -/
def twoSeedXL : Fin 1 → ℝ := fun _ => 0

/-- The positions of the right seed of the two-seed word. -/
def twoSeedXR : Fin 1 → ℝ := fun _ => 0

/-! ### Named inputs: `0 < κ < 4` -/

/-- **Named input (κ < 4, continuity and transience): the revised induction for Theorem 1.3, `0 < κ < 4`**
(Specification §7.3, `source/spec/p337-384.md` L843–L878, pp. 378–380, with Aux. lemmas 99, 106, 113; cited in
LP11's proof, p. 488: "the retained independent finite-force induction proves continuity through every finite
continuation threshold and transience on infinite lifetime"). Every ordered force word is complete for every
`0 < κ < 4`. Packet PROVE-SEC7-C. -/
def RevisedInductionLtFourStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input (κ < 4, determination): Lemma 7.5 with Aux. lemmas 52–55** (Specification p. 252 and
pp. 244–247; LP11's proof, p. 488: "Lemma 7.5 and Aux. 52–55 supply the independent finite-force determining
graph"). For `0 < κ < 4` and every ordered force word, the killed driving history of every coupling satisfying the
optional hull specification of Theorem 1.1 is a Borel function of the field. Packet PROVE-SEC7-A. -/
def Lemma75DeterminationStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → HasFieldDeterminedHistories.{u} κ xL xR ρL ρR

/-! ### Named inputs: `κ = 4` (Wang–Wu, ruling R31) -/

/-- **Named input (κ = 4, determination): Theorem 1.7 of the Wang–Wu document** (`source/external/WW17LP/
wang_wu_lean_preprocessed.pdf`, p. 3, = [WW17] Theorem 1.1.2; ruling R31), on the frozen carriers: for force data
as in its Definition 1.2 (the frozen ordered force word, as in `WangWu/Defs.lean`), "the complete killed marked chain
is measurable with respect to `F`, after completion by null sets", for every coupling of the marked chain with the
field — here every coupling satisfying the optional hull specification of Theorem 1.1 at `κ = 4` (`λ = π/2`,
`dW = 2 dB`), which the specification identifies with Wang–Wu's normalization (LP11 proof, p. 488). Note: the
document states the assertion for the coupling of its Theorem 1.6 and for "any coupling satisfying the full
stopping-time local-set conditional laws of Definition 1.5 and the same SDE law"; the frozen optional hull
specification prescribes the conditional law of the field away from the filled hull. Packets PROVE-WW-A/B. -/
def WWTheorem17Statement : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → HasFieldDeterminedHistories.{u} 4 xL xR ρL ρR

/-- **Named input (κ = 4, continuity and transience): Theorem 1.8 of the Wang–Wu document** (p. 3, = [WW17]
Theorem 1.1.3; ruling R31), on the frozen carriers: for force data as in its Definition 1.2 (the frozen ordered force
word), the marked `SLE₄(ρ)` chain (any integrated evolution, by Theorem 2.2 = the document's input 8.1) is almost
surely generated by a continuous curve on `[0, T)`, extended continuously to a finite endpoint when `0 < T < ∞`, and
tending to `∞` on `{T = ∞}`; the frozen `IsGeneratingTrace` on `[0, T]` with `‖η‖ → ∞` on `{T = ∞}`. Packets
PROVE-WW-A/C. If only the distinct-position form `WWTheorem18DistinctStatement` is proved, this statement follows by
amalgamation (`LPAmalgamate.lean`, `wwTheorem18Statement_of_distinct`). -/
def WWTheorem18Statement : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → IsCompleteForceWord.{u} 4 xL xR ρL ρR

/-- `WWTheorem18Statement` for force data with distinct positions on each side (the literal list form of the
Wang–Wu document's Definition 1.2). -/
def WWTheorem18DistinctStatement : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsDistinctForceWord xL xR → IsCompleteForceWord.{u} 4 xL xR ρL ρR

/-- `WWTheorem17Statement` for force data with distinct positions on each side. -/
def WWTheorem17DistinctStatement : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsDistinctForceWord xL xR → HasFieldDeterminedHistories.{u} 4 xL xR ρL ρR

/-- **Amalgamation of coincident marks, trace form** (a reduction, not an input; **proved** in `LPAmalgamate.lean`,
`coincidentMarksTraceStatement`). If every force word with distinct positions on each side is complete at `κ`, so is
every ordered force word: coincident marks of one side have equal force coordinates (Wang–Wu Lemma 2.1) and enter
the driving equation and the threshold only through their summed weight (Specification p. 378, "Amalgamate
coincident groups on the same side by adding their weights"; LP10's proof, p. 486). -/
def CoincidentMarksTraceStatement (κ : ℝ) : Prop :=
  (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      IsDistinctForceWord xL xR → IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      IsOrderedForceWord xL xR → IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Amalgamation of coincident marks, determination form** (a reduction, not an input; not proved, and not used
by the assembly below). As `CoincidentMarksTraceStatement`, for field determination of the killed driving history
(the boundary data `forceBoundaryData` only see the summed weights, and the amalgamated driving filtration agrees with
the original one up to null sets). It would derive `WWTheorem17Statement` from `WWTheorem17DistinctStatement`. -/
def CoincidentMarksDeterminationStatement (κ : ℝ) : Prop :=
  (∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      IsDistinctForceWord xL xR → HasFieldDeterminedHistories.{u} κ xL xR ρL ρR) →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      IsOrderedForceWord xL xR → HasFieldDeterminedHistories.{u} κ xL xR ρL ρR

/-! ### Named inputs: `κ > 4` -/

/-- **Named input (κ > 4, determination): Corollary LP7** (p. 487, its first assertion): for `k > 4` and every finite
force word, the complete integrated driving and force-coordinate history up to its continuation threshold is a
measurable function of the coupling field, for every coupling with the original optional hull specification. -/
def LP7DeterminationStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR → HasFieldDeterminedHistories.{u} κ xL xR ρL ρR

/-- **Named input (κ > 4): Theorem LP10** (p. 486), with its independent inputs (the one-force first-swallow
theorem Aux. lemma 99 and the whole-history buffered comparisons Aux. lemmas 108–111, §7.3) included: for `k > 4`,
if the two-seed word is complete for every admissible pair `r_L, r_R > −2`, then every ordered force word is
complete. -/
def LP10Statement : Prop :=
  ∀ κ : ℝ, 4 < κ →
    (∀ rL rR : ℝ, -2 < rL → -2 < rR →
      IsCompleteForceWord.{u} κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR)) →
    ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
      IsOrderedForceWord xL xR → IsCompleteForceWord.{u} κ xL xR ρL ρR

/-- **Named input (κ > 4): Theorem R.7** (p. 477, its consequence "the integrated `SLE_k(r_L; r_R)` driving law has
this continuous transient trace"): for `k > 4`, `r_L, r_R > −2` and `max(r_L, r_R) ≥ d = k/2 − 4`, the two-seed
word is complete. -/
def TheoremR7TraceStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR → κ / 2 - 4 ≤ max rL rR →
    IsCompleteForceWord.{u} κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR)

/-- **Named input (κ > 4): Lemma 7.25** (p. 413, in the form used by LP4, LP5 and LP11: "Lemma 7.25 already supplies
finite-time trace continuity"): for `κ' > 4` and `ρ^L, ρ^R ∈ (−2, κ'/2 − 4)`, every integrated two-seed evolution
almost surely has a continuous generating trace (on every finite capacity interval). -/
def Lemma725TraceStatement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η

/-- **Named input (κ > 4): Proposition LP4** (p. 482): for `k > 4` and `−2 < r_L, r_R < c = k/2 − 2`, if the
canonical two-seed driving law has a continuous trace on every finite capacity interval, then this trace tends to
infinity almost surely. -/
def LP4Statement : Prop :=
  ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 2 → -2 < rR → rR < κ / 2 - 2 →
    (∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η → ζ ω = ⊤ →
          Tendsto (fun t => ‖η t‖) atTop atTop

/-- **The two-seed inputs of LP10** ("Two-seed inputs to the induction", p. 487; LP11's proof, p. 488): for `k > 4`,
Theorem R.7 supplies every admissible pair with `max(r_L, r_R) ≥ d`, and Lemma 7.25 with LP4 the strict both-low
rectangle (`d < c`). -/
theorem isCompleteForceWord_twoSeed (hR7 : TheoremR7TraceStatement.{u})
    (h725 : Lemma725TraceStatement.{u}) (hLP4 : LP4Statement.{u}) {κ : ℝ} (hκ : 4 < κ) {rL rR : ℝ}
    (hL : -2 < rL) (hR : -2 < rR) :
    IsCompleteForceWord.{u} κ twoSeedXL twoSeedXR (fun _ => rL) (fun _ => rR) := by
  by_cases hd : κ / 2 - 4 ≤ max rL rR
  · exact hR7 κ hκ rL rR hL hR hd
  have hd' := not_le.1 hd
  have hLd : rL < κ / 2 - 4 := lt_of_le_of_lt (le_max_left _ _) hd'
  have hRd : rR < κ / 2 - 4 := lt_of_le_of_lt (le_max_right _ _) hd'
  intro P _ 𝓕 W VL VR B ζ hE
  have hcont := h725 κ hκ rL rR hL hLd hR hRd P 𝓕 W VL VR B ζ hE
  have htrans := hLP4 κ hκ rL rR hL (by linarith) hR (by linarith)
    (fun P' _ 𝓕' W' VL' VR' B' ζ' hE' => h725 κ hκ rL rR hL hLd hR hRd P' 𝓕' W' VL' VR' B' ζ' hE')
    P 𝓕 W VL VR B ζ hE
  filter_upwards [hcont, htrans] with ω h1 h2
  obtain ⟨η, hη⟩ := h1
  exact ⟨η, hη, h2 η hη⟩

/-! ### Corollary LP11: Theorems 1.2–1.3 for every parameter -/

/-- **Corollary LP11, continuity part = the frozen Theorem 1.3** (`IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace`,
same conclusion), assembled from the named inputs by LP11's three parameter ranges (p. 488): the revised §7.3
induction for `0 < κ < 4`; Wang–Wu's Theorem 1.8 (R31) for `κ = 4`; and for
`κ > 4` Theorem LP10, whose two-seed inputs are Theorem R.7, Lemma 7.25 and Proposition LP4. The inadmissible-seed
assertion is proved (`IsIntegratedSLEEvolution.ae_eq_zero_of_thresholdCondition`). -/
theorem ae_exists_isGeneratingTrace_of_inputs (hLT4 : RevisedInductionLtFourStatement.{u})
    (hWW : WWTheorem18Statement.{u}) (hLP10 : LP10Statement.{u}) (hR7 : TheoremR7TraceStatement.{u})
    (h725 : Lemma725TraceStatement.{u}) (hLP4 : LP4Statement.{u})
    {a : ℝ} (ha : 0 < a) {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, (ForceWord.ThresholdCondition ρL ρR 0 xL xR → ζ ω = 0) ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
        (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  have hc : IsCompleteForceWord.{u} a xL xR ρL ρR := by
    rcases lt_trichotomy a 4 with h | rfl | h
    · exact hLT4 a ha h xL xR ρL ρR hF
    · exact hWW xL xR ρL ρR hF
    · exact hLP10 a h (fun rL rR hL hR => isCompleteForceWord_twoSeed hR7 h725 hLP4 h hL hR)
        xL xR ρL ρR hF
  exact ae_exists_isGeneratingTrace_of_isCompleteForceWord hc hE

/-- **Corollary LP11, determination part = the frozen Theorem 1.2** (`exists_measurable_lifetime_trace_eq_comp_field`,
same conclusion), assembled from the named driving-determination inputs by LP11's three parameter ranges (p. 488):
Lemma 7.5 with Aux. 52–55 for `0 < κ < 4`; Wang–Wu's Theorem 1.7 (R31) for `κ = 4`; Corollary LP7 for `κ > 4`; then the proved deterministic reconstruction of the entire trace from the driving
history (LP11, pp. 488–489; `exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory`). -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_inputs
    (hLT4 : Lemma75DeterminationStatement.{u}) (hWW : WWTheorem17Statement.{u})
    (hLP7 : LP7DeterminationStatement.{u})
    (κ : ℝ) (hκ : 0 < κ) {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (hF : IsOrderedForceWord xL xR) {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hcoup : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal := by
  have hdet : HasFieldDeterminedHistories.{u} κ xL xR ρL ρR := by
    rcases lt_trichotomy κ 4 with h4 | rfl | h4
    · exact hLT4 κ hκ h4 xL xR ρL ρR hF
    · exact hWW xL xR ρL ρR hF
    · exact hLP7 κ h4 xL xR ρL ρR hF
  exact exists_measurable_lifetime_trace_eq_comp_field_of_isFieldDeterminedHistory hcoup
    (hdet P 𝓕 W VL VR B ζ h hcoup)

end LP

end InteractingSLE
