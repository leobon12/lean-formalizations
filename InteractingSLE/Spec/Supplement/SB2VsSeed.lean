/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsSample

/-!
# The relative seed and the relative gauge at the start (D19, step 4)

Packet PROVE-AUX61-NOJUMP (decision D19).

* **`pos_cellGauge_zero`** (deterministic): for a word with marks `xL ≤ 0 ≤ xR` whose seed is not at its threshold,
  the capped distance of `0` to the closed bad set is positive: by `Vr.mem_badSet_or_mark_of_mem_closure` a limit
  point of the bad set is bad or a nonzero mark, and `0` is bad exactly at a seed threshold.
* **`SB2RelSeedAdmStatement`** (named input; E7 at time `0`): almost surely on the entrance event, the relative seed of
  the launch word's type is not at its threshold. It is forced by SB2DRV's interface `Lv.SB2LineVersionS`: there the
  stops are positive (`ann`) and at most the threshold on every type cell (`V_le_thr`), and the threshold of a
  continuous driver from `0` is `0` at a bad seed. It is the time-`0` case of E7's direction (hlt), "no relative
  threshold before the relative lifetime", which decision D18 assigns to PROVE-T14-SB2WORD.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Finset
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vs

open Vr Vq Exist.Staged Exist.StagedLaw Lv Supp8.Q3Stop

/-- **An admissible seed keeps `0` off the closed bad set.** -/
theorem pos_cellGauge_zero {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) :
    0 < min (infEDist 0 (closure (badSet xL xR ρL ρR))) 1 := by
  refine lt_min ?_ one_pos
  rw [infEDist_pos_iff_notMem_closure, closure_closure]
  intro h0
  rcases mem_badSet_or_mark_of_mem_closure hxR hxL h0 with hb | ⟨j, hj0, hj⟩ | ⟨i, hi0, hi⟩
  · apply hseed
    rcases hb.2 with ⟨-, hw⟩ | ⟨-, hw⟩
    · right
      have e : univ.filter (fun j => xR j = 0) = univ.filter (fun j => xR j ≤ (0 : ℂ).re) := by
        refine Finset.filter_congr fun j _ => ?_
        simp only [Complex.zero_re]
        exact ⟨le_of_eq, fun h => le_antisymm h (hxR j)⟩
      rw [e]; exact hw
    · left
      have e : univ.filter (fun i => xL i = 0) = univ.filter (fun i => (0 : ℂ).re ≤ xL i) := by
        refine Finset.filter_congr fun i _ => ?_
        simp only [Complex.zero_re]
        exact ⟨ge_of_eq, fun h => le_antisymm (hxL i) h⟩
      rw [e]; exact hw
  · exact hj0 (by exact_mod_cast hj.symm)
  · exact hi0 (by exact_mod_cast hi.symm)

/-- **Named input (E7 at time `0`; D18 assigns E7's direction (hlt) to PROVE-T14-SB2WORD)**: almost surely on the
entrance event, the relative seed of the launch word's type is not at its threshold. -/
def SB2RelSeedAdmStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (_HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀),
    ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ I.word D.event w →
      ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) 0 (cellXL κ ψ I.word w ω) (cellXR κ ψ I.word w ω)

/-- **The relative gauge at the start is positive** on a type cell with an admissible seed. -/
theorem pos_relGauge_zero {Ω : Type*} {κ ψ : ℝ} {cw : Ω → Restart.BoundaryWord} {types : Set WordType}
    {ω : Ω} {w : WordType} (hw : w ∈ types) (hcell : angleWordType κ ψ (cw ω) = w)
    (hseed : ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) 0 (cellXL κ ψ cw w ω)
      (cellXR κ ψ cw w ω)) :
    0 < relGauge κ ψ cw types ω 0 := by
  rw [relGauge_eq κ ψ cw types hw hcell]
  exact pos_cellGauge_zero (Restart.FCDet.isOrderedForceWord_typeXL (cw ω)).2.1
    (Restart.FCDet.isOrderedForceWord_typeXL (cw ω)).2.2.2 hseed

end InteractingSLE.Theorem14.SB.Vs
