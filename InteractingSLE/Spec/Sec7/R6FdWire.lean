/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FdPath

/-!
# R.6's non-corner input (bounded mixed shape) from the shared-arc visit

Packet PROVE-R6-FACE3. PROVE-R6-FACE2's named input `R6Fc.R6NonCornerMixedRemaining` (the outer landing of the shared
seed coordinate is a non-corner point of `∂U`) splits into (F0) the reverse visit order of the shared wall, (F1) the
landing identification and (F2) the exclusion of `U`'s entrance corner `y₀ᵁ`. (F0) is `U`'s own `revL`/`revR`
(`IsCfPocketConfig`: the shared wall is a wall of `U`); (F1) is `R6FdLand.landR_spec`/`landL_spec`; the combination is
`R6FdPath.nonCornerLanding_left/_right`. What remains is (F2), stated here as the named input
`R6SharedArcVisitMixedRemaining`:

> almost surely on the nested event at `(s, q)`, the relative trace of the outer pocket has visited the **open shared
> arc** of the inner pocket `U` by the relative time `q`.

This is false deterministically (the counterflow may enter `U` at `y₀ᵁ` and wander in `U` without touching its shared
arc) but true almost surely: `U`'s relative traversal is the two-seed SLE_κ′ with shared-side weight `≤ κ′/2 − 4 <
κ′/2 − 2`, whose force-point process is a Bessel process of dimension `< 2` started at `0`, hence returns to `0` at
times accumulating at `0⁺`; every such return is a visit of `U`'s open shared arc by `U`'s erased path, hence by the
outer erased path before the same physical time. See the handoff for the source's own argument at the corner and why
the landed face route cannot use it.

* `sharedArc`: the open shared arc of the inner pocket;
* `R6SharedArcVisitMixedRemaining` (**named, unproved**, the corrected (F2) input);
* **`r6NonCornerMixedRemaining_of_sharedArcVisit`**: `R6SharedArcVisitMixedRemaining → R6Fc.R6NonCornerMixedRemaining`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open QuantumZipper (H Hbar chiC)
open LQGMetric (DistOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.R6Fd

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly R6Safe WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert PocketMarks PocketSeedOpen
  PocketStopWallsFin PocketStopSide

universe u

/-- **The open shared arc of the inner pocket** `cfPocket R' L' r'`: its open left arc when the shared wall is the left
wall (`d < r_L`, `d = κ′/2 − 4`), its open right arc otherwise. -/
def sharedArc (k rL : ℝ) (R' L' : ℝ≥0 → ℂ) (r' : ℝ≥0) : Set ℂ :=
  if k / 2 - 4 < rL then cfArcL R' L' r' '' Ioo 0 1 else cfArcR R' L' r' '' Ioo 0 1

/-- **Named, unproved: the outer relative trace visits the inner pocket's open shared arc** (the corrected (F2)
input; mixed shapes, bounded outer pocket; the binders of `R6Fc.R6NonCornerMixedRemaining`): almost surely on the
nested event at `(s, q)`, some relative time `u₁` with capacity `≤ q` has its relative tip on the open shared arc of
`U`. -/
def R6SharedArcVisitMixedRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ u₁ : ℝ, 0 ≤ u₁ ∧ capClock (travAll R L r η ψ ω) u₁ ≤ q ∧
          relTip R L r η u₁ ω ∈ sharedArc k rL (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)

/-- **R.6's non-corner input from the shared-arc visit** (bounded outer pocket, mixed shapes). -/
theorem r6NonCornerMixedRemaining_of_sharedArcVisit {k rL rR c c' : ℝ}
    (hV : R6SharedArcVisitMixedRemaining.{u} k rL rR c c') : R6Fc.R6NonCornerMixedRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hVer MR ML hMR hML r A A' ψ ψ' n s q hA hA'
  filter_upwards [hV hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hVer MR ML hMR hML r A A' ψ ψ' s q hA
    hA'] with ω hω hωA hωA' hωN
  obtain ⟨u₁, hu₁0, hcap₁, harc⟩ := hω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hq0' : 0 < StripSys.rt q := by
    show 0 < (q : ℝ).toNNReal
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq0)
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hU := hA' ω hωA'
  rcases hmix with ⟨hdL, hdR⟩ | ⟨hdL, hdR⟩
  · have eR : innerRight k rL R MR ω = MR ω := by simp only [innerRight, hdL, ↓reduceIte]
    have eL : innerLeft k rR L ML ω = L ω := by simp only [innerLeft, not_lt.2 hdR, ↓reduceIte]
    simp only [sharedArc, hdL, ↓reduceIte] at harc
    simp only [hdL, ↓reduceIte]
    rw [eR, eL] at hU hsub hrel harc ⊢
    exact nonCornerLanding_left (W := fun ω t => W' t.toNNReal ω) (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) hωA hU.1 hU.2 hq0' hqlive hsub hu0 (by rw [hrtq]; exact hcap) hrel hu₁0
      (by rw [hrtq]; exact hcap₁) harc
  · have eR : innerRight k rL R MR ω = R ω := by simp only [innerRight, not_lt.2 hdL, ↓reduceIte]
    have eL : innerLeft k rR L ML ω = ML ω := by simp only [innerLeft, hdR, ↓reduceIte]
    simp only [sharedArc, not_lt.2 hdL, ↓reduceIte] at harc
    simp only [not_lt.2 hdL, ↓reduceIte]
    rw [eR, eL] at hU hsub hrel harc ⊢
    exact nonCornerLanding_right (W := fun ω t => W' t.toNNReal ω) (fun ω hω => (hA ω hω).1)
      (fun ω hω => (hA ω hω).2) hωA hU.1 hU.2 hq0' hqlive hsub hu0 (by rw [hrtq]; exact hcap) hrel hu₁0
      (by rw [hrtq]; exact hcap₁) harc

end InteractingSLE.Sec7.R6Fd
