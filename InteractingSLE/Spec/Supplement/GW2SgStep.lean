/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgVer
import InteractingSLE.Spec.Supplement.GW2RdStgEngine

/-!
# GW2's stage identity: the stage step (version restriction + GB6's engine)

Packet PROVE-GW2-RELDET, ruling R106. This file composes the landed stage pieces into ONE stage step.

**`ae_isStopDrvMatch_stage`**: the inputs are
* an announced R-form version `(R, V, ρ, ρs)` of the WHOLE relative exploration;
* a stage record `x` (e.g. `GW2Rd.stageEncRec`) with measurable decoders `σ`, `A`, `pre`: the record, the relative
  start, and an almost surely continuous relative prefix agreeing with `R` up to the start;
* K2's inputs `HasRelSafe k w β E` for EVERY word type, for the joint law of `x` and the STAGE relative variable
  `(Hr, stgDrv R (A x), V − A x)`.

The conclusion: almost surely on the stage record event, the stage relative driver matches the canonical angle-`0`
code `Fd` of `(β x, Hr)` up to the stage stop.

The proof is `GW2Rd.ae_isStopDrvMatch_rec` with the stage path rules `GW2Rd.stageRule ρ σ A pre` and
`stageRule (ρs n) σ A pre`. `stgVersion_inputs_ae` is `GW2Rd.stgVersion_inputs` with the prefix continuous only almost
surely (records outside the support need not decode to a continuous path). Conditional helpers with distinct names.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Restart Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId

/-- **The engine's version inputs at a stage**, with a prefix continuous only almost surely. -/
theorem stgVersion_inputs_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {R : ℝ≥0 → Ω → ℝ}
    (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    {rec x : Ω → RecData} (hx : Measurable x) {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun u => R u ω)) {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρsfin : ∀ n y, ρs n y ≠ ⊤) (hρsmono : ∀ y, Monotone fun n => ρs n y) {G : Set Ω}
    (hann : ∀ᵐ ω ∂P, ω ∈ G → (∀ n, ρs n (rec ω, fun u => R u ω) < V ω) ∧
      ⨆ n, ρs n (rec ω, fun u => R u ω) = V ω)
    {σ : RecData → RecData} {A : RecData → ℝ≥0} (hA : Measurable A) {pre : RecData → ℝ≥0 → ℝ}
    (hprec : ∀ᵐ ω ∂P, Continuous (pre (x ω)))
    (hdec : ∀ᵐ ω ∂P, σ (x ω) = rec ω ∧ ∀ t ≤ A (x ω), pre (x ω) t = R t ω)
    (hstart : ∀ᵐ ω ∂P, ω ∈ G → (A (x ω) : ℝ≥0∞) < V ω) :
    (∀ t, Measurable fun ω => stgDrv (fun u => R u ω) (A (x ω)) t) ∧
    (∀ ω, Continuous fun t => stgDrv (fun u => R u ω) (A (x ω)) t) ∧
    (∀ ω, stgDrv (fun u => R u ω) (A (x ω)) 0 = 0) ∧
    Measurable (fun ω => V ω - A (x ω)) ∧
    (∀ᵐ ω ∂P, ω ∈ G → 0 < V ω - A (x ω)) ∧
    (∀ᵐ ω ∂P, V ω - A (x ω) = stageRule ρ σ A pre (x ω, fun t => stgDrv (fun u => R u ω) (A (x ω)) t)) ∧
    (∀ n y, stageRule (ρs n) σ A pre y ≠ ⊤) ∧ (∀ y, Monotone fun n => stageRule (ρs n) σ A pre y) ∧
    (∀ᵐ ω ∂P, ω ∈ G → ∀ n,
      stageRule (ρs n) σ A pre (x ω, fun t => stgDrv (fun u => R u ω) (A (x ω)) t) < V ω - A (x ω)) ∧
    (∀ᵐ ω ∂P, ω ∈ G →
      ⨆ n, stageRule (ρs n) σ A pre (x ω, fun t => stgDrv (fun u => R u ω) (A (x ω)) t) = V ω - A (x ω)) := by
  have hAm : Measurable fun ω => A (x ω) := hA.comp hx
  have hstg : ∀ᵐ ω ∂P, ∀ (ρ' : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞),
      stageRule ρ' σ A pre (x ω, fun t => stgDrv (fun u => R u ω) (A (x ω)) t) =
        ρ' (rec ω, fun u => R u ω) - A (x ω) := by
    filter_upwards [hdec, hprec] with ω hω hc ρ'
    exact stageRule_stgDrv (hRc ω) hc hω.1 hω.2
  refine ⟨fun t => measurable_stgDrv hRm hRc hAm t, fun ω => continuous_stgDrv (hRc ω) _,
    fun ω => stgDrv_zero _ _, hVm.sub (measurable_coe_nnreal_ennreal.comp hAm), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hstart] with ω hω hG using tsub_pos_of_lt (hω hG)
  · filter_upwards [hstg, hVρ] with ω hω hV
    rw [hω ρ, hV]
  · intro n y
    exact ne_top_of_le_ne_top (hρsfin n _) tsub_le_self
  · intro y n m hnm
    exact tsub_le_tsub_right (hρsmono _ hnm) _
  · filter_upwards [hstg, hann, hstart] with ω hω ha hs hG n
    rw [hω]
    rcases le_or_gt (A (x ω) : ℝ≥0∞) (ρs n (rec ω, fun u => R u ω)) with hle | hlt
    · exact ((ENNReal.cancel_of_ne ENNReal.coe_ne_top).tsub_lt_tsub_iff_right hle).2 ((ha hG).1 n)
    · rw [tsub_eq_zero_of_le hlt.le]
      exact tsub_pos_of_lt (hs hG)
  · filter_upwards [hstg, hann] with ω hω ha hG
    simp only [hω]
    rw [← ENNReal.iSup_sub, (ha hG).2]

/-- **The stage step**: an announced version of the whole relative exploration, measurable stage-record decoders and
K2's inputs at the stage give the stopped driver match of the stage relative driver with the canonical code. -/
theorem ae_isStopDrvMatch_stage {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℝ} (hk : 0 < k) {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode k 0 Fd) {β : RecData → BoundaryWord} (hβ : Measurable β) {E : Set RecData}
    (hE : MeasurableSet E) (hcount : (range fun r : RecData => wordType k (β r)).Countable)
    {x : Ω → RecData} (hx : Measurable x) {Hr : Ω → DistOn upperHalfPlaneOpens} (hHr : Measurable Hr)
    {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    {V : Ω → ℝ≥0∞} (hVm : Measurable V) {rec : Ω → RecData} {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hρm : Measurable ρ) (hρ : IsPathRule ρ) (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun u => R u ω))
    {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n)) (hρs : ∀ n, IsPathRule (ρs n))
    (hρsfin : ∀ n y, ρs n y ≠ ⊤) (hρsmono : ∀ y, Monotone fun n => ρs n y) {G : Set Ω}
    (hann : ∀ᵐ ω ∂P, ω ∈ G → (∀ n, ρs n (rec ω, fun u => R u ω) < V ω) ∧
      ⨆ n, ρs n (rec ω, fun u => R u ω) = V ω)
    {σ : RecData → RecData} (hσ : Measurable σ) {A : RecData → ℝ≥0} (hA : Measurable A)
    {pre : RecData → ℝ≥0 → ℝ} (hpre : ∀ t, Measurable fun r => pre r t)
    (hprec : ∀ᵐ ω ∂P, Continuous (pre (x ω)))
    (hdec : ∀ᵐ ω ∂P, σ (x ω) = rec ω ∧ ∀ t ≤ A (x ω), pre (x ω) t = R t ω)
    (hstart : ∀ᵐ ω ∂P, ω ∈ G → (A (x ω) : ℝ≥0∞) < V ω) (hEG : ∀ᵐ ω ∂P, x ω ∈ E → ω ∈ G)
    (hS : ∀ w : WordType, HasRelSafe k w β E (P.map fun ω => (x ω, relVar Hr
      (fun t ω => stgDrv (fun u => R u ω) (A (x ω)) t) (fun ω => V ω - A (x ω)) ω))) :
    ∀ᵐ ω ∂P, x ω ∈ E → IsStopDrvMatch (Fd (β (x ω), Hr ω))
      (fun t => stgDrv (fun u => R u ω) (A (x ω)) t) (V ω - A (x ω)) := by
  obtain ⟨hRnm, hRnc, hRn0, hVnm, hV0, hVρn, hρsfin', hρsmono', hlt, hsup⟩ :=
    stgVersion_inputs_ae (P := P) hRm hRc hVm hx hVρ hρsfin hρsmono hann hA hprec hdec hstart
  refine ae_isStopDrvMatch_rec hk hFd hβ hE hcount hx hHr hRnm hRnc hRn0 hVnm hS ?_
    (measurable_stageRule hρm hσ hA hpre) (isPathRule_stageRule hρ σ A pre) hVρn
    (fun n => measurable_stageRule (hρsm n) hσ hA hpre) (fun n => isPathRule_stageRule (hρs n) σ A pre)
    hρsfin' hρsmono' ?_ ?_
  · filter_upwards [hV0, hEG] with ω h1 h2 hm using h1 (h2 hm)
  · filter_upwards [hlt, hEG] with ω h1 h2 hm using h1 (h2 hm)
  · filter_upwards [hsup, hEG] with ω h1 h2 hm using h1 (h2 hm)

end InteractingSLE.Theorem14.GW2Rd
