/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdeStage
import InteractingSLE.Spec.Supplement.GW2SkStep
import InteractingSLE.Spec.Supplement.GW2SkFilt

/-!
# GW2's retained stopped SDE: the stage variable of a GB6 exploration on the augmented stage record

Packet PROVE-GW2-SDE (round 2). At stage `T` of GB6's relative exploration (explored driver `W`, retained curve
`Wα, ζα` at `s`, good set `GT`, an announced R-form version `(R, V, ρ, ρs)`), PROVE-GW2-RELDET's stage objects are the
augmented stage record `augRec x (stgPreRec … T R)` (the stage-start history `x` with the record of the relative prefix,
`GW2SkRec`), the stage relative driver `stgDrv R (stgStart T)` and the stage stop `V − stgStart T`. This file packs
them into a `StageVar` and proves its `StageVar.IsSafe` from:

* the GLOBAL announced version (`IsGB6RelVersion` plus the path rule `ρ` of the cap and the announcing rules `ρs`);
* the stage-start history decoding to GB6's counterflow record (`stgRecDec N (x ω) = gb6Rec …`);
* good live stage records on `E` (the counterflow record good and the stage started before the cap);
* the stage K2 law `HasRelSafe` on every word type (the stage lines, `GW2SdeLines`), the word properties, the stop.

The engine conditions at the stage (the stage cap a path rule of the stage record and the stage path, announced) are
DERIVED: they are `GW2Rd.stageRule` of the global rules with the exact decoders `augσ`, `augA`, `augPre`
(`GW2Rd.stgVersion_inputs_ae`, `GW2Rd.augDec_spec`).

* `stgR`, `stgV`, `stgRec`: the stage relative driver, the stage cap and the augmented stage record;
* `augStageVar`: the stage variable; **`isSafe_augStageVar`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sde

open GW2KM2 Restart Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe
  GW2Rd

section Defs

variable {Ω : Type u}

/-- The stage relative driver: GB6's relative driver restarted at the stage start. -/
abbrev stgR (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (T : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => stgDrv (fun u => R u ω) (stgStart s W Wα ζα GT V T ω) t

/-- The stage cap: GB6's cap minus the stage start. -/
abbrev stgV (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (V : Ω → ℝ≥0∞) (T : ℝ≥0) :
    Ω → ℝ≥0∞ :=
  fun ω => V ω - stgStart s W Wα ζα GT V T ω

/-- The augmented stage record: the stage-start history `x` with the record of the relative prefix. -/
abbrev stgRec (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (T : ℝ≥0) (x : Ω → RecData) : Ω → RecData :=
  augRec x (stgPreRec s W Wα ζα GT V T R)

/-- **The stage variable of stage `T`** on the augmented record: the augmented record, the stage driver and cap, the
stage rules of the global cap rules with the exact decoders, and the given word, record event, stage field and
physical stop. -/
def augStageVar (s : ℝ≥0) (W Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (GT : Set Ω) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    (T : ℝ≥0) (x : Ω → RecData) (N : ℕ) (ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞) (β : RecData → BoundaryWord) (E : Set RecData)
    (Hr : Ω → DistOn upperHalfPlaneOpens) (stop : Ω → ℝ≥0∞) (stopRule : RecData → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞) :
    StageVar Ω where
  record := stgRec s W Wα ζα GT R V T x
  β := β
  E := E
  Hr := Hr
  R := stgR s W Wα ζα GT R V T
  V := stgV s W Wα ζα GT V T
  ρ := stageRule ρ (augσ N) augA augPre
  ρs := fun n => stageRule (ρs n) (augσ N) augA augPre
  stop := stop
  stopRule := stopRule

end Defs

/-- **The safe stage law of the augmented stage variable**: the engine conditions at the stage are derived from the
global announced version (conditional helper: the stage `HasRelSafe`, the good live record event, the word
properties and the stop data are hypotheses). -/
theorem isSafe_augStageVar {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {GT : Set Ω} {R : ℝ≥0 → Ω → ℝ}
    {V : Ω → ℝ≥0∞} (hv : IsGB6RelVersion s P W Wα ζα γ α R V) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρm : Measurable ρ) (hρ : IsPathRule ρ) (hVρ : ∀ᵐ ω ∂P, V ω = ρ (gb6Rec s Wα ζα ω, fun u => R u ω))
    {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n)) (hρs : ∀ n, IsPathRule (ρs n))
    (hρsfin : ∀ n y, ρs n y ≠ ⊤) (hρsmono : ∀ y, Monotone fun n => ρs n y)
    (hann : ∀ᵐ ω ∂P, gb6Rec s Wα ζα ω ∈ gb6TS s → (∀ n, ρs n (gb6Rec s Wα ζα ω, fun u => R u ω) < V ω) ∧
      ⨆ n, ρs n (gb6Rec s Wα ζα ω, fun u => R u ω) = V ω)
    {T : ℝ≥0} {N : ℕ} {x : Ω → RecData} (hx : Measurable x) (hxrec : ∀ ω, stgRecDec N (x ω) = gb6Rec s Wα ζα ω)
    (hpre : Measurable (stgPreRec s W Wα ζα GT V T R)) {κ : ℝ} {β : RecData → BoundaryWord} (hβ : Measurable β)
    {E : Set RecData} (hE : MeasurableSet E) (hcount : (range fun r : RecData => wordType κ (β r)).Countable)
    (hsort : ∀ r ∈ E, (β r).IsSorted)
    (hEgood : ∀ᵐ ω ∂P, stgRec s W Wα ζα GT R V T x ω ∈ E →
      gb6Rec s Wα ζα ω ∈ gb6TS s ∧ (stgStart s W Wα ζα GT V T ω : ℝ≥0∞) < V ω)
    {Hr : Ω → DistOn upperHalfPlaneOpens} (hHr : Measurable Hr)
    (hS : ∀ w : WordType, HasRelSafe κ w β E (P.map fun ω => (stgRec s W Wα ζα GT R V T x ω,
      relVar Hr (stgR s W Wα ζα GT R V T) (stgV s W Wα ζα GT V T) ω)))
    {stop : Ω → ℝ≥0∞} {stopRule : RecData → (ℝ≥0 → ℝ) × ℝ≥0∞ → ℝ≥0∞}
    (hstopRule : ∀ (y : RecData) (t : ℝ≥0), MeasurableSet[pathKilledSigma t] {e | stopRule y e ≤ (t : ℝ≥0∞)})
    (hstopm : Measurable stop)
    (hstopEq : ∀ᵐ ω ∂P, stop ω = stopRule (stgRec s W Wα ζα GT R V T x ω)
      ((fun t => stgR s W Wα ζα GT R V T t ω), stgV s W Wα ζα GT V T ω))
    (hstopLe : ∀ᵐ ω ∂P, stgRec s W Wα ζα GT R V T x ω ∈ E → stop ω ≤ stgV s W Wα ζα GT V T ω)
    (hstopLt : ∀ᵐ ω ∂P, stgRec s W Wα ζα GT R V T x ω ∈ E → stop ω ≠ ⊤ → stop ω < stgV s W Wα ζα GT V T ω) :
    (augStageVar s W Wα ζα GT R V T x N ρ ρs β E Hr stop stopRule).IsSafe κ P (stgRec s W Wα ζα GT R V T x) := by
  have hRm := hv.1
  have hRc := hv.2.1
  have hR0 := hv.2.2.1
  have hVm := hv.2.2.2.2.1
  set z : Ω → RecData := stgRec s W Wα ζα GT R V T x with hzdef
  have hz : Measurable z := measurable_augRec hx hpre
  have hdec : ∀ ω, augσ N (z ω) = gb6Rec s Wα ζα ω ∧ augA (z ω) = stgStart s W Wα ζα GT V T ω ∧
      ∀ t ≤ augA (z ω), augPre (z ω) t = R t ω := fun ω => augDec_spec (hxrec ω) (hRc ω) (hR0 ω)
  have hAe : ∀ ω, augA (z ω) = stgStart s W Wα ζα GT V T ω := fun ω => (hdec ω).2.1
  set G : Set Ω := {ω | gb6Rec s Wα ζα ω ∈ gb6TS s ∧ (stgStart s W Wα ζα GT V T ω : ℝ≥0∞) < V ω} with hGdef
  obtain ⟨hRnm, hRnc, hRn0, hVnm, hV0, hVρn, hρsfin', hρsmono', hlt, hsup⟩ :=
    stgVersion_inputs_ae (P := P) hRm hRc hVm hz hVρ hρsfin hρsmono (G := G)
      (hann.mono fun ω h hG => h hG.1) measurable_augA (Eventually.of_forall fun ω => continuous_augPre (z ω))
      (Eventually.of_forall fun ω => ⟨(hdec ω).1, (hdec ω).2.2⟩)
      (Eventually.of_forall fun ω hG => (hAe ω).symm ▸ hG.2)
  simp only [hAe] at hRnm hRnc hRn0 hVnm hV0 hVρn hlt hsup
  have hEG : ∀ᵐ ω ∂P, z ω ∈ E → ω ∈ G := hEgood
  refine ⟨hβ, hE, hcount, hsort, hHr, hRnm, hRnc, hRn0, hVnm, hS, ?_,
    measurable_stageRule hρm (measurable_augσ N) measurable_augA measurable_augPre,
    isPathRule_stageRule hρ (augσ N) augA augPre, hVρn,
    fun n => measurable_stageRule (hρsm n) (measurable_augσ N) measurable_augA measurable_augPre,
    fun n => isPathRule_stageRule (hρs n) (augσ N) augA augPre, hρsfin', hρsmono', ?_, ?_, hstopRule, hstopm,
    hstopEq, hstopLe, hstopLt⟩
  · filter_upwards [hV0, hEG] with ω h1 h2 hm using h1 (h2 hm)
  · filter_upwards [hlt, hEG] with ω h1 h2 hm using h1 (h2 hm)
  · filter_upwards [hsup, hEG] with ω h1 h2 hm using h1 (h2 hm)

end InteractingSLE.Theorem14.GW2Sde
