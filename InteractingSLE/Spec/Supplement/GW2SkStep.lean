/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SkRec
import InteractingSLE.Spec.Supplement.GW2SgStep

/-!
# GW2's stage identity: the stage step on the augmented stage record

Packet PROVE-GW2-RELDET, ruling R106. `GW2Rd.ae_isStopDrvMatch_stage` with the EXACT decoders of the augmented stage
record (`GW2SkRec`): the record is `augRec x (stgPreRec … T R)` (the stage-start history `x`, decoding to GB6's
counterflow record, together with the record of the relative prefix). Then the stage relative driver is exactly
`stgDrv R (stgStart T)` and the stage stop exactly `V − stgStart T`, the objects of the stage lines
(`GW2SkFilt`, `GW2SkSafe`).

**`ae_isStopDrvMatch_stage_aug`**. The inputs are:
* an announced R-form version of the WHOLE relative exploration;
* the stage starting before the stop on the good event;
* K2's inputs `HasRelSafe k w β E` at the stage, for all word types.

The output: the stage relative driver matches the canonical code of `(β record, Hr)` up to the stage stop, almost
surely on the record event. No decoder hypothesis remains. Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Restart Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId Supp8.RelSafe

/-- **The stage step on the augmented stage record.** -/
theorem ae_isStopDrvMatch_stage_aug {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {s : ℝ≥0} {W Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {GT : Set Ω} {T : ℝ≥0}
    {k : ℝ} (hk : 0 < k) {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode k 0 Fd) {β : RecData → BoundaryWord} (hβ : Measurable β) {E : Set RecData}
    (hE : MeasurableSet E) (hcount : (range fun r : RecData => wordType k (β r)).Countable)
    {N : ℕ} {x : Ω → RecData} (hx : Measurable x) {Hr : Ω → DistOn upperHalfPlaneOpens} (hHr : Measurable Hr)
    {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hR0 : ∀ ω, R 0 ω = 0) {V : Ω → ℝ≥0∞} (hVm : Measurable V) {rec : Ω → RecData}
    (hxrec : ∀ ω, stgRecDec N (x ω) = rec ω) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρm : Measurable ρ) (hρ : IsPathRule ρ) (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun u => R u ω))
    {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n)) (hρs : ∀ n, IsPathRule (ρs n))
    (hρsfin : ∀ n y, ρs n y ≠ ⊤) (hρsmono : ∀ y, Monotone fun n => ρs n y) {G : Set Ω}
    (hann : ∀ᵐ ω ∂P, ω ∈ G → (∀ n, ρs n (rec ω, fun u => R u ω) < V ω) ∧
      ⨆ n, ρs n (rec ω, fun u => R u ω) = V ω)
    (hpre : Measurable (stgPreRec s W Wα ζα GT V T R))
    (hstart : ∀ᵐ ω ∂P, ω ∈ G → (stgStart s W Wα ζα GT V T ω : ℝ≥0∞) < V ω)
    (hEG : ∀ᵐ ω ∂P, augRec x (stgPreRec s W Wα ζα GT V T R) ω ∈ E → ω ∈ G)
    (hS : ∀ w : WordType, HasRelSafe k w β E (P.map fun ω => (augRec x (stgPreRec s W Wα ζα GT V T R) ω,
      relVar Hr (fun t ω => stgDrv (fun u => R u ω) (stgStart s W Wα ζα GT V T ω) t)
        (fun ω => V ω - stgStart s W Wα ζα GT V T ω) ω))) :
    ∀ᵐ ω ∂P, augRec x (stgPreRec s W Wα ζα GT V T R) ω ∈ E →
      IsStopDrvMatch (Fd (β (augRec x (stgPreRec s W Wα ζα GT V T R) ω), Hr ω))
        (fun t => stgDrv (fun u => R u ω) (stgStart s W Wα ζα GT V T ω) t) (V ω - stgStart s W Wα ζα GT V T ω) := by
  set z : Ω → RecData := augRec x (stgPreRec s W Wα ζα GT V T R) with hzdef
  have hz : Measurable z := measurable_augRec hx hpre
  have hdec : ∀ ω, augσ N (z ω) = rec ω ∧ augA (z ω) = stgStart s W Wα ζα GT V T ω ∧
      ∀ t ≤ augA (z ω), augPre (z ω) t = R t ω := fun ω => augDec_spec (hxrec ω) (hRc ω) (hR0 ω)
  have hAe : ∀ ω, augA (z ω) = stgStart s W Wα ζα GT V T ω := fun ω => (hdec ω).2.1
  -- the engine's stage objects coincide with the physical stage objects
  have hS' : ∀ w : WordType, HasRelSafe k w β E (P.map fun ω => (z ω, relVar Hr
      (fun t ω => stgDrv (fun u => R u ω) (augA (z ω)) t) (fun ω => V ω - augA (z ω)) ω)) := by
    intro w
    simp only [hAe]
    exact hS w
  have h := ae_isStopDrvMatch_stage (P := P) hk hFd hβ hE hcount hz hHr hRm hRc hVm hρm hρ hVρ hρsm hρs hρsfin
    hρsmono hann (measurable_augσ N) measurable_augA measurable_augPre
    (Eventually.of_forall fun ω => continuous_augPre (z ω))
    (Eventually.of_forall fun ω => ⟨(hdec ω).1, (hdec ω).2.2⟩)
    (hstart.mono fun ω h hG => by rw [hAe]; exact h hG) hEG hS'
  simp only [hAe] at h
  exact h

end InteractingSLE.Theorem14.GW2Rd
