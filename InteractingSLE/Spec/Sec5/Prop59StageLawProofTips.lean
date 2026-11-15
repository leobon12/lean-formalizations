/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageLawProofBridge
import InteractingSLE.Spec.Sec5.Prop59StageLawProofWords
import InteractingSLE.Spec.Sec5.Prop59StageTips
import InteractingSLE.Spec.Sec5.CrossCondMart

/-!
# Proposition 5.9's alternating construction from the delivered piece laws

Packet PROVE-PROP59T3. Assembly of PROVE-PROP59T2's experiment (`ae_not_isBounded_of_stageLaw`,
`tip0UnboundedStatement_of_stageLaw`, `tipUnboundedStatement_of_stageLaw`) with

* the disintegration step (`Prop59StageLawProofBridge`): the stage law `Prop59StageLawStatement` from the piece laws
  `Prop59StagePieceLawStatement` (each new extreme-angle piece is an integrated evolution with an initially
  measurable random word, given the revealed history);
* the stage-word conditions `hwL`, `hwR` from the initial word (`Prop59StageLawProofWords`, `IsStageInit`).

**The root-`0` initial word.** At root `0` the first piece is the flow line given the counterflow history, read in the
counterflow chart: PROVE-GLUECOND10's image word with the junction weights of R57,
`(jwL cL6 κ ρL; jwR cR6 κ ρR)` (`CrossCond.Word49.exists_isWordEntrance_of_filtW` with
`imageWord49FiltCStatement`), for a flow word with the non-boundary-intersecting bounds (4.4) (`Sec4.Cond44`, the
hypothesis of GLUECOND10's law). `isStageInit_jw` shows that this word satisfies `IsStageInit`: the junction weights
make the totals `κ − 4` and `κ/2 − 2`, the left prefix sums of (4.4) are `≥ κ/2 − 2` and its right ones `≥ 0`. Hence
`hwL` and `hwR` hold for it at every depth (`hwL_jw`, `hwR_jw`).

## Main results

* **`isStageInit_jw`**, **`hwL_jw`**, **`hwR_jw`**: the root-`0` image word satisfies the stage-word conditions;
* **`ae_not_isBounded_of_pieceLaw`**: the experiment from the piece laws, the stage system and `IsStageInit`;
* **`tip0UnboundedStatement_of_pieceLaw`**, **`tipUnboundedStatement_of_pieceLaw`**: PROVE-PROP59T's statements from
  the same inputs (no `hwL`/`hwR`, no stage-law hypothesis).

Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE

namespace Sec5

namespace Prop59Stage

/-! ### The root-`0` image word -/

section ImageWord

open CrossCond.Word49

variable {κ : ℝ} {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The root-`0` image word satisfies the initial-word conditions**: for a flow word with the bounds (4.4), the
image word `(jwL cL6 κ ρL; jwR cR6 κ ρR)` of PROVE-GLUECOND10 (junction weights `κ − 4 − Σρ_L`, `κ/2 − 2 − Σρ_R`)
satisfies `IsStageInit`. -/
theorem isStageInit_jw (h44 : Sec4.Cond44 κ ρL ρR) : IsStageInit κ (jwL cL6 κ ρL) (jwR cR6 κ ρR) := by
  refine ⟨?_, ?_, fun m hm1 hm => ?_, fun m hm1 hm => ?_⟩
  · rw [jwL, psum_snoc_succ, cL6]; ring
  · rw [jwR, psum_snoc_succ, cR6]; ring
  · rw [jwL, psum_snoc_of_le _ _ (by omega)]
    exact h44.1 m hm1 (by omega)
  · rw [jwR, psum_snoc_of_le _ _ (by omega)]
    exact h44.2 m hm1 (by omega)

/-- **`hwL` for the root-`0` image word.** -/
theorem hwL_jw (hκ : 0 < κ) (hκ4 : κ < 4) (h44 : Sec4.Cond44 κ ρL ρR) :
    ∀ j, Even j → IsStageWordN κ (stageρL κ (jwL cL6 κ ρL) j) (stageρR κ (jwR cR6 κ ρR) j) :=
  hwL_of_isStageInit hκ hκ4 (isStageInit_jw h44)

/-- **`hwR` for the root-`0` image word.** -/
theorem hwR_jw (hκ : 0 < κ) (hκ4 : κ < 4) (h44 : Sec4.Cond44 κ ρL ρR) :
    ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ (jwR cR6 κ ρR) j) (stageρL κ (jwL cL6 κ ρL) j) :=
  hwR_of_isStageInit hκ hκ4 (isStageInit_jw h44)

end ImageWord

/-! ### The experiment from the piece laws -/

section Main

variable {κ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL₀ nR₀ : ℕ} {hnL : 0 < nL₀} {hnR : 0 < nR₀} {Q : Set ℝ≥0} {δ : ℕ → ℝ≥0}
  {G : ℕ → ℕ → ℝ≥0} {sys : StageSys Ω nL₀ nR₀} {C : Ω → Set ℂ} {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}

/-- **The alternating construction from the piece laws** (proof of Proposition 5.9, pp. 143–148): if every stage
piece has the delivered law (`Prop59StagePieceLawStatement`), the realized construction has the structure
`IsStageSystem`, and the initial word satisfies `IsStageInit`, then almost surely on the initial event the node
images are unbounded. -/
theorem ae_not_isBounded_of_pieceLaw (hκ : 0 < κ) (hκ4 : κ < 4)
    (hL : Prop59StagePieceLawStatement κ P ρL₀ ρR₀ sys) (hS : IsStageSystem P hnL hnR Q δ G sys C)
    (hI : IsStageInit κ ρL₀ ρR₀) (r₀ : ℕ → ℕ) :
    ∀ᵐ ω ∂P, ω ∈ (sys r₀ 0).R → ¬ Bornology.IsBounded (C ω) :=
  ae_not_isBounded_of_stageLaw hκ hκ4 (prop59StageLawStatement_of_pieceLaw hL) hS
    (hwL_of_isStageInit hκ hκ4 hI) (hwR_of_isStageInit hκ hκ4 hI) r₀

end Main

section Tips

open Prop59Tips

variable {κ : ℝ} {Ω : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL₀ nR₀ : ℚ → ℕ} {hnL : ∀ r, 0 < nL₀ r} {hnR : ∀ r, 0 < nR₀ r}
  {ρL₀ : (r : ℚ) → Fin (nL₀ r) → ℝ} {ρR₀ : (r : ℚ) → Fin (nR₀ r) → ℝ} {Q : Set ℝ≥0} {δ : ℚ → ℕ → ℝ≥0}
  {G : ℚ → ℕ → ℕ → ℝ≥0} {sys : (r : ℚ) → StageSys Ω (nL₀ r) (nR₀ r)}

/-- **`Tip0UnboundedStatement` from the piece laws** (root `0`): as `tip0UnboundedStatement_of_stageLaw`, with the
stage law replaced by the delivered piece laws and the word conditions by `IsStageInit` of the initial words. -/
theorem tip0UnboundedStatement_of_pieceLaw (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ} {z : ℕ → Ω → ℂ}
    (hL : ∀ r : ℚ, 0 < r → Prop59StagePieceLawStatement κ P (ρL₀ r) (ρR₀ r) (sys r))
    (hS : ∀ r : ℚ, 0 < r → IsStageSystem P (hnL r) (hnR r) Q (δ r) (G r) (sys r) fun ω =>
      (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
        (range (fun n => z n ω) ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal)))
    (hI : ∀ r : ℚ, 0 < r → IsStageInit κ (ρL₀ r) (ρR₀ r))
    (hR0 : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, ω ∈ (sys r (fun _ => 0) 0).R) :
    Tip0UnboundedStatement P W z :=
  tip0UnboundedStatement_of_stageLaw hκ hκ4 (fun r hr => prop59StageLawStatement_of_pieceLaw (hL r hr)) hS
    (fun r hr => hwL_of_isStageInit hκ hκ4 (hI r hr)) (fun r hr => hwR_of_isStageInit hκ hκ4 (hI r hr)) hR0

/-- **`TipUnboundedStatement` from the piece laws** (root `z`): as `tipUnboundedStatement_of_stageLaw`, with the stage
law replaced by the delivered piece laws and the word conditions by `IsStageInit` of the initial words. -/
theorem tipUnboundedStatement_of_pieceLaw (hκ : 0 < κ) (hκ4 : κ < 4) {W : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}
    {z : Ω → ℂ} {S : Ω → Set ℂ}
    (hL : ∀ r : ℚ, 0 < r → Prop59StagePieceLawStatement κ P (ρL₀ r) (ρR₀ r) (sys r))
    (hS : ∀ r : ℚ, 0 < r → IsStageSystem P (hnL r) (hnR r) Q (δ r) (G r) (sys r) fun ω =>
      (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 ''
        (S ω ∩ (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal)))
    (hI : ∀ r : ℚ, 0 < r → IsStageInit κ (ρL₀ r) (ρR₀ r))
    (hR0 : ∀ r : ℚ, 0 < r → ∀ᵐ ω ∂P, (r : ℝ) < traceFirstVisit (γ ω) (z ω) → ω ∈ (sys r (fun _ => 0) 0).R) :
    TipUnboundedStatement P W γ z S :=
  tipUnboundedStatement_of_stageLaw hκ hκ4 (fun r hr => prop59StageLawStatement_of_pieceLaw (hL r hr)) hS
    (fun r hr => hwL_of_isStageInit hκ hκ4 (hI r hr)) (fun r hr => hwR_of_isStageInit hκ hκ4 (hI r hr)) hR0

end Tips

end Prop59Stage

end Sec5

end InteractingSLE
