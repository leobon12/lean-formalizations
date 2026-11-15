/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgLines

/-!
# GW2's stage identity: GB6's engine on every word type of an arbitrary record

Packet PROVE-GW2-RELDET, ruling R106. At stage `n` the engine conditions on the encoded stage-start history
(`GW2RdStgEnc.stageEncRec`), not on the counterflow record alone, and its word is the stage word. The stage-`0`
wrapper `GW2Rd.ae_isStopDrvMatch_gw2` is tied to the counterflow record; this file gives the record-generic form.

* **`ae_isStopDrvMatch_rec`**: if the relative variable `(Hr, R, V)` of a measurable record `rec` has K2's inputs
  `HasRelSafe k w β E` for EVERY word type `w`, the word types of `β` form a countable set, the stop is positive on
  the record event, a measurable path rule of (record, path), and announced by measurable finite path rules, then
  almost surely on `{rec ∈ E}` the relative driver matches the canonical angle-`0` code `Fd` of `(β rec, Hr)` up to
  the stop (`Q3Stop.ae_isStopDrvMatch_of_hasRelSafe` on each type, intersected over the countable types).

Conditional helper with a distinct name.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Restart Supp8.GB6 Supp8.GB6.RelDrv Supp8.Q3Stop Supp8.GB6.HullId

/-- **GB6's engine for an arbitrary record, on all word types at once.** -/
theorem ae_isStopDrvMatch_rec {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℝ} (hk : 0 < k) {Fd : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hFd : IsCanonicalDriverCode k 0 Fd) {β : RecData → BoundaryWord} (hβ : Measurable β) {E : Set RecData}
    (hE : MeasurableSet E) (hcount : (range fun r : RecData => wordType k (β r)).Countable)
    {rec : Ω → RecData} (hrecm : Measurable rec) {Hr : Ω → DistOn upperHalfPlaneOpens} (hHr : Measurable Hr)
    {R : ℝ≥0 → Ω → ℝ} (hRm : ∀ t, Measurable (R t)) (hRc : ∀ ω, Continuous fun t => R t ω)
    (hR0 : ∀ ω, R 0 ω = 0) {V : Ω → ℝ≥0∞} (hVm : Measurable V)
    (hS : ∀ w : WordType, HasRelSafe k w β E (P.map fun ω => (rec ω, relVar Hr R V ω)))
    (hV0 : ∀ᵐ ω ∂P, rec ω ∈ E → 0 < V ω)
    {ρ : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρm : Measurable ρ) (hρ : IsPathRule ρ)
    (hVρ : ∀ᵐ ω ∂P, V ω = ρ (rec ω, fun u => R u ω))
    {ρs : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞} (hρsm : ∀ n, Measurable (ρs n)) (hρs : ∀ n, IsPathRule (ρs n))
    (hρsfin : ∀ n x, ρs n x ≠ ⊤) (hρsmono : ∀ x, Monotone fun n => ρs n x)
    (hρslt : ∀ᵐ ω ∂P, rec ω ∈ E → ∀ n, ρs n (rec ω, fun u => R u ω) < V ω)
    (hρssup : ∀ᵐ ω ∂P, rec ω ∈ E → ⨆ n, ρs n (rec ω, fun u => R u ω) = V ω) :
    ∀ᵐ ω ∂P, rec ω ∈ E → IsStopDrvMatch (Fd (β (rec ω), Hr ω)) (fun t => R t ω) (V ω) := by
  have hw : ∀ w : WordType, ∀ᵐ ω ∂P, rec ω ∈ E → wordType k (β (rec ω)) = w →
      IsStopDrvMatch (Fd (β (rec ω), Hr ω)) (fun t => R t ω) (V ω) := fun w =>
    ae_isStopDrvMatch_of_hasRelSafe hk hFd hβ hE w hrecm hHr hRm hRc hR0 hVm (hS w) hV0 hρm hρ hVρ hρsm hρs hρsfin
      hρsmono hρslt hρssup
  have hall := (ae_ball_iff hcount).2 fun w _ => hw w
  filter_upwards [hall] with ω hω hm
  exact hω _ ⟨_, rfl⟩ hm rfl

end InteractingSLE.Theorem14.GW2Rd
