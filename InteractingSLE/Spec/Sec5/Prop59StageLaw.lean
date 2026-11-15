/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59TipsCross
import InteractingSLE.Spec.Sec5.Heights

/-!
# Proposition 5.9's alternating construction: the stage law

Packet PROVE-PROP59T2. Specification §5.2, proof of Proposition 5.9 (`source/spec/p097-144.md` L1000–L1016,
`p145-192.md` L1–L72, pp. 143–147). The alternating extreme-angle construction is a sequence of *stages*. At the start
of stage `s = j + 1` (after `j` switches), conditionally on the already revealed history (the counterflow up to `r`
and the flow prefix through the start of the stage), the next flow-line piece, read in the joint chart `ψ` (prefix
mapped out, prefix tip `↦` current driver, counterflow tip `↦ ∞`), is an integrated `SLE_κ(ρ)` evolution of the
Figure 5.8 word from the current configuration:

> Condition on the entire already revealed history. If we use the extreme angle `−e_j π/2`, the full-span case of
> Aux. lemma 22 and the boundary calculation below show […]. At a switch the new two force points start at the driver
> […]. All other marks are separated from the driver; coincident initial marks, if any, are first amalgamated.

This file states that law **in the form the experiment consumes it** (`IsStageLaw`):

* almost surely on the event `R` that the stage is reached, the stage start is an ordered force word with distinct
  positions on each side, and the piece is an integrated path from it (Definition 2.1, killed at its continuation
  threshold; the flow line is the piece before its first new boundary contact);
* **the conditional law given the past is the `SLE_κ(ρ)` law from the start**, in comparison form: for every Borel set
  `S` of (start, rational-time samples of the killed state) and every `p`, if every integrated evolution (with an
  almost surely existing generating trace) from every start `y₀` gives the section of `S` at `y₀` probability at
  least `p`, then `p P(A) ≤ P(A ∩ {(start, samples) ∈ S})` for every past event `A ⊆ R`.

The comparison form is the regular-conditional-law statement tested on Borel events; by Theorem 2.2's uniqueness in
law every evolution from `y₀` gives the same probability to such an event, so it says that the conditional law of the
piece's samples given the past is the canonical law from the (past-measurable) start. Only lower bounds are used.

The words are deterministic: from an initial word `(ρL₀; ρR₀)` (stage 1), each switch prepends one new mark on each
side at the driver with the angle-change weights `ρ^{1,L} = −ρ^{1,R} = ± πχ/λ` (`stageρL`, `stageρR`; the sign
alternates with the stage, p. 146: `ρ^{i,R} = (χ/λ)(θ_{j−i+1} − θ_{j−i})`).

The objects are indexed by a **rule** `r : ℕ → ℕ` (the switching-grid index used at each stage) and the depth `j`
(`StageSys`); the construction of the rule is part of the experiment (`Prop59StageExp`).

## Main definitions

* `Samp`, `samp`: rational-time samples of a killed state; `measurable_samp_of_evolution`;
* `IsStageLaw`, `stageρL`, `stageρR`, `StageData`, `StageSys`;
* **`Prop59StageLawStatement`** (the named input of PROVE-PROP59T2): every stage of the stage system satisfies
  `IsStageLaw` with the deterministic stage word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

namespace Prop59Stage

/-! ### Rational-time samples of a killed state -/

section Samp

variable {nL nR : ℕ}

/-- The rational-time samples of a killed state: its lifetime and its values at the nonnegative rationals before the
lifetime (`0` after it). -/
abbrev Samp (nL nR : ℕ) := ℝ≥0∞ × (ℚ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))

/-- The rational-time samples of the killed state `(w, v_L, v_R)` with lifetime `ζ`. -/
def samp (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Samp nL nR :=
  (ζ, fun q => if ((q : ℝ≥0) : ℝ≥0∞) < ζ then (w q, fun i => vL i q, fun k => vR k q) else 0)

theorem samp_fst (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (ζ : ℝ≥0∞) :
    (samp w vL vR ζ).1 = ζ := rfl

theorem samp_snd_of_lt (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) {ζ : ℝ≥0∞} {q : ℚ≥0}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) < ζ) :
    (samp w vL vR ζ).2 q = (w q, fun i => vL i q, fun k => vR k q) := by
  simp only [samp, hq, ↓reduceIte]

/-- The samples of the killed state of processes adapted before `ζ` are measurable. -/
theorem measurable_samp_of_adaptedBefore {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hW : AdaptedBefore 𝓕 ζ W) (hVL : ∀ i, AdaptedBefore 𝓕 ζ (VL i))
    (hVR : ∀ k, AdaptedBefore 𝓕 ζ (VR k)) :
    Measurable fun ω => samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω) := by
  have hζ : Measurable ζ := by
    have h := Ito.isStoppingTime_lifetime hW
    have hm : Measurable fun ω => (ζ ω : WithTop ℝ≥0) := h.measurable'
    exact hm
  refine hζ.prodMk (measurable_pi_iff.2 fun q => ?_)
  have hlt : MeasurableSet {ω | ((q : ℝ≥0) : ℝ≥0∞) < ζ ω} := measurableSet_lt measurable_const hζ
  have hkill : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓕 ζ X →
      Measurable fun ω => if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then X q ω else 0 := fun hX =>
    Sec2.Assembly.measurable_killedAt hX q
  have e : (fun ω => if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then
      ((W q ω, fun i => VL i q ω, fun k => VR k q ω) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) else 0) =
      fun ω => ((if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then W q ω else 0),
        (fun i => if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then VL i q ω else 0),
        fun k => if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then VR k q ω else 0) := by
    funext ω
    by_cases h : ((q : ℝ≥0) : ℝ≥0∞) < ζ ω
    · simp only [h, ↓reduceIte]
    · simp only [h, ↓reduceIte]; rfl
  show Measurable fun ω => (if ((q : ℝ≥0) : ℝ≥0∞) < ζ ω then
      ((W q ω, fun i => VL i q ω, fun k => VR k q ω) : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) else 0)
  rw [e]
  exact (hkill hW).prodMk ((measurable_pi_iff.2 fun i => hkill (hVL i)).prodMk
    (measurable_pi_iff.2 fun k => hkill (hVR k)))

/-- The samples of an integrated evolution are measurable. -/
theorem measurable_samp_of_evolution {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    Measurable fun ω => samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω) :=
  measurable_samp_of_adaptedBefore hE.2.1 hE.2.2.1 hE.2.2.2.1

end Samp

/-! ### The stage law -/

/-- A stage start: the absolute driver position (in the joint chart `ψ`) and the left and right force positions
relative to the driver. -/
abbrev Start (nL nR : ℕ) := ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)

/-- **The law of one stage** (Proposition 5.9, pp. 143–145, in the form the experiment consumes it). `𝓠` is the past
(the revealed history at the start of the stage), `R ∈ 𝓠` the event that the stage is reached, `y` the stage start
(absolute driver, relative positions) and `(W, V_L, V_R, B, ζ)` the piece relative to its start, with the word
`(ρL; ρR)`. The two clauses:

1. almost surely on `R`, the start is an ordered force word with distinct positions on each side, and the piece is
   an integrated path of Definition 2.1 from it;
2. **the conditional law of the piece given `𝓠` is the `SLE_κ(ρ)` law from the start**, tested on Borel events of
   (start, samples): if every integrated evolution from every `y₀` (on any probability space, with an almost surely
   existing generating trace) gives the section of `S` at `y₀` probability at least `p`, then every past event
   `A ⊆ R` satisfies `p P(A) ≤ P(A ∩ {(start, samples) ∈ S})`. -/
def IsStageLaw (κ : ℝ) {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝓠 : MeasurableSpace Ω)
    (R : Set Ω) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (y : Ω → Start nL nR)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) : Prop :=
  (∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧ StrictMono (y ω).2.2 ∧
    IsIntegratedSLEPath κ (y ω).2.1 (y ω).2.2 ρL ρR (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω)
      (B · ω) (ζ ω)) ∧
  ∀ S : Set (Start nL nR × Samp nL nR), MeasurableSet S → ∀ p : ℝ≥0∞,
    (∀ (y₀ : Start nL nR) (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') [IsProbabilityMeasure P']
      (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
      (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
      IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' →
      (∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω') (ζ' ω') η) →
      p ≤ P' {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')) ∈ S}) →
    ∀ A : Set Ω, MeasurableSet[𝓠] A → A ⊆ R →
      p * P A ≤ P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S})

/-! ### The stage words -/

/-- The new left weight created at the `j`-th switch (`j = 0, 1, …`; the switch ending stage `j + 1`):
`(−1)^j πχ/λ` (left weights are the negatives of the right ones, p. 146). -/
def newL (κ : ℝ) (j : ℕ) : ℝ := (-1) ^ j * angleWeightBound κ

/-- The new right weight created at the `j`-th switch: `−(−1)^j πχ/λ`. -/
def newR (κ : ℝ) (j : ℕ) : ℝ := -((-1) ^ j * angleWeightBound κ)

/-- **Prepending a sequence of new weights**: `consAlt c ρ₀ m` has the `m` new weights `c (m − 1), …, c 0` at the
indices `0, …, m − 1` (the most recent next to the driver) followed by the initial weights `ρ₀`. -/
def consAlt (c : ℕ → ℝ) {n₀ : ℕ} (ρ₀ : Fin n₀ → ℝ) : (m : ℕ) → Fin (n₀ + m) → ℝ
  | 0 => ρ₀
  | m + 1 => Fin.cons (c m) (consAlt c ρ₀ m)

/-- **The left weights at depth `j`** (after `j` switches): the new marks are prepended at index `0`, next to the
driver; the initial marks keep the last indices. -/
def stageρL (κ : ℝ) {nL₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (j : ℕ) : Fin (nL₀ + j) → ℝ := consAlt (newL κ) ρL₀ j

/-- **The right weights at depth `j`.** -/
def stageρR (κ : ℝ) {nR₀ : ℕ} (ρR₀ : Fin nR₀ → ℝ) (j : ℕ) : Fin (nR₀ + j) → ℝ := consAlt (newR κ) ρR₀ j

theorem stageρL_zero (κ : ℝ) {nL₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) : stageρL κ ρL₀ 0 = ρL₀ := rfl

theorem stageρL_succ (κ : ℝ) {nL₀ : ℕ} (ρL₀ : Fin nL₀ → ℝ) (j : ℕ) :
    stageρL κ ρL₀ (j + 1) = Fin.cons (newL κ j) (stageρL κ ρL₀ j) := rfl

theorem stageρR_succ (κ : ℝ) {nR₀ : ℕ} (ρR₀ : Fin nR₀ → ℝ) (j : ℕ) :
    stageρR κ ρR₀ (j + 1) = Fin.cons (newR κ j) (stageρR κ ρR₀ j) := rfl

/-! ### The stage system -/

/-- **The data of one stage** in the joint chart `ψ` (fixed counterflow time `r` and root): the past `past`, the event
`R` that the stage is reached, the start `y`, the piece `(W, V_L, V_R, B, ζ)` relative to its start (the
constant-angle continuation, killed at its continuation threshold), and its **original clock** `clk` (the original
capacity time of the flow line as a function of the piece's `ψ`-capacity time; switching times are chosen in the
prescribed countable set `Q` of the original clock). -/
structure StageData (Ω : Type*) (nL nR : ℕ) where
  /-- The revealed history at the start of the stage. -/
  past : MeasurableSpace Ω
  /-- The stage is reached (all earlier stages succeeded). -/
  R : Set Ω
  /-- The stage start: absolute driver, relative left and right positions. -/
  y : Ω → Start nL nR
  /-- The relative driver of the piece. -/
  W : ℝ≥0 → Ω → ℝ
  /-- The relative left force points. -/
  VL : Fin nL → ℝ≥0 → Ω → ℝ
  /-- The relative right force points. -/
  VR : Fin nR → ℝ≥0 → Ω → ℝ
  /-- The driving Brownian motion of the piece. -/
  B : ℝ≥0 → Ω → ℝ
  /-- The lifetime (continuation threshold) of the piece. -/
  ζ : Ω → ℝ≥0∞
  /-- The original clock of the piece. -/
  clk : Ω → ℝ≥0 → ℝ≥0

/-- **A stage system**: for every rule `r` (the grid index used at each stage) and depth `j`, the data of stage
`j + 1`, with `nL₀ + j` left and `nR₀ + j` right marks. -/
abbrev StageSys (Ω : Type*) (nL₀ nR₀ : ℕ) := (ℕ → ℕ) → (j : ℕ) → StageData Ω (nL₀ + j) (nR₀ + j)

/-- **Named input of PROVE-PROP59T2: the stage law of Proposition 5.9's alternating construction.** Every stage of the
stage system obeys `IsStageLaw` with the deterministic stage word `(stageρL κ ρL₀ j; stageρR κ ρR₀ j)`: conditionally
on the revealed counterflow and flow prefix, the next extreme-angle piece in the joint chart is an integrated
`SLE_κ(ρ)` evolution of the Figure 5.8 word from the current configuration. -/
def Prop59StageLawStatement (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {nL₀ nR₀ : ℕ}
    (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) (sys : StageSys Ω nL₀ nR₀) : Prop :=
  ∀ (r : ℕ → ℕ) (j : ℕ), IsStageLaw κ P (sys r j).past (sys r j).R (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
    (sys r j).y (sys r j).W (sys r j).VL (sys r j).VR (sys r j).B (sys r j).ζ

/-! ### Consuming the comparison form -/

section Consume

variable {κ : ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓠 : MeasurableSpace Ω} {R : Set Ω}
  {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The premise of the comparison form for a start set `D`: every integrated evolution from a start in `D` gives the
section of `S` at that start probability at least `p`. -/
def CompPremise (κ : ℝ) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (D : Set (Start nL nR))
    (S : Set (Start nL nR × Samp nL nR)) (p : ℝ≥0∞) : Prop :=
  ∀ y₀ ∈ D, ∀ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') [IsProbabilityMeasure P']
    (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
    (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
    IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' →
    (∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω') (ζ' ω') η) →
    p ≤ P' {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')) ∈ S}

/-- **The comparison form restricted to a start set `D`**: if every evolution from a start in `D` gives the section of
`S` probability at least `p`, then `p P(A) ≤ P(A ∩ {y ∈ D → (y, samples) ∈ S})` for past events `A ⊆ R`. -/
theorem IsStageLaw.le_measure (hL : @IsStageLaw κ Ω mΩ P 𝓠 R nL nR ρL ρR y W VL VR B ζ) {D : Set (Start nL nR)}
    (hD : MeasurableSet D) {S : Set (Start nL nR × Samp nL nR)} (hS : MeasurableSet S) {p : ℝ≥0∞} (hp1 : p ≤ 1)
    (hp : CompPremise κ ρL ρR D S p) {A : Set Ω} (hA : MeasurableSet[𝓠] A) (hAR : A ⊆ R) :
    p * P A ≤ P (A ∩ {ω | y ω ∈ D → (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := by
  have hS' : MeasurableSet ((Prod.fst ⁻¹' Dᶜ) ∪ S) := (measurable_fst hD.compl).union hS
  have h := hL.2 _ hS' p (fun y₀ Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr => by
    by_cases hy : y₀ ∈ D
    · refine (hp y₀ hy Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE htr).trans (measure_mono fun ω' hω' => ?_)
      exact Or.inr hω'
    · have : {ω' | (y₀, samp (W' · ω') (fun i t => VL' i t ω') (fun k t => VR' k t ω') (ζ' ω')) ∈
          (Prod.fst ⁻¹' Dᶜ) ∪ S} = univ := by
        ext ω'
        simp only [mem_union, mem_preimage, mem_compl_iff, hy, not_false_eq_true, true_or, mem_ofPred_eq,
          mem_univ]
      rw [this, measure_univ]
      exact hp1) A hA hAR
  refine h.trans (measure_mono fun ω hω => ⟨hω.1, fun hyD => ?_⟩)
  rcases hω.2 with h1 | h1
  · exact absurd hyD h1
  · exact h1

end Consume

end Prop59Stage

end Sec5

end InteractingSLE
