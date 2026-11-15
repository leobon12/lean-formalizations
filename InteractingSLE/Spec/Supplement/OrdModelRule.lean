/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.OrdModelCarrier
import InteractingSLE.Spec.Supplement.OrdAStopModel
import InteractingSLE.Spec.Restart.FCK2SourceCollision

/-!
# The A-stop is a Galmarino rule of the killed history, given the code

Packet PROVE-T15-ASTOP2. Ruling R79: the stopped-hull extension may only be applied to stops given by a measurable
Galmarino rule of the stopped model's own killed driving history (`Aux54.stoppedHullExtendRStatement`); the consumer
used by PROVE-T15-ASTOP (`StoppedTypeModelJ.ae_codeMatch`, through the arbitrary-stop
`StoppedExtend.StoppedHullExtendStatement`) is the defective form. The A-stop reads the A-set, which is not a function
of the driving history; it is a rule of the history **once the initial code is fixed**:

* `aStopRule ρL ρR c`: the first positive time at which the trace read from the history meets the decoded A-set
  `codeJ c` (closed pieces `aStopPiece c m`, times `≥ 1/(m+1)`), or the first threshold of the state read from the
  history, whichever comes first (the form of `FlowStopIdentG.flowRule`); measurable and strongly Galmarino for every
  `c` (`measurable_aStopRule`, `isHistGalmarino_aStopRule`);
* **`aStopRule_killedHistory`**: on a sample where the trace generates the driver up to `V > 0`, `V ≤ thr`, the trace
  avoids `codeJ c` at positive times before `V`, and a finite `V` is the threshold or a contact, the rule reads `V` from
  the history killed at `V`;
* `HasCodeHistoryRule M`: a model with an initial code whose lifetime is `R (code) (killed history)` for a family of
  measurable Galmarino rules `R c` (the R79-safe form for models with codes).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.RLC.OrdModel

open Restart Restart.FlowStopIdentG LawUnique Restart.StoppedExtendWF Restart.RetAux79 Sec7.PocketTraversal
  Restart.FCDet OrdAStop

variable {nL nR : ℕ}

/-- The `m`th closed piece of the positive-time contacts with the decoded A-set. -/
def aStopPiece (c : ℝ) (m : ℕ) : Set (ℝ≥0 × ℂ) := {p | (1 : ℝ≥0) / (m + 1) ≤ p.1 ∧ p.2 ∈ codeJ c}

theorem isClosed_aStopPiece (c : ℝ) (m : ℕ) : IsClosed (aStopPiece c m) :=
  (isClosed_le continuous_const continuous_fst).inter ((isClosed_codeJ c).preimage continuous_snd)

/-- **The A-stop rule with code `c`**: the first detected positive-time contact of the trace with `codeJ c`, or the
first threshold of the state, whichever comes first. -/
def aStopRule (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (c : ℝ) : HistorySpace nL nR → ℝ≥0∞ :=
  fun γ => min (hitRuleSeq retTimedTrace (aStopPiece c) γ) (hitRuleSeq histState (thrSet ρL ρR) γ)

theorem measurable_aStopRule (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (c : ℝ) : Measurable (aStopRule ρL ρR c) :=
  (measurable_hitRuleSeq (fun p => measurable_retTimedTrace (dyadicTime p)) _).min
    (measurable_hitRuleSeq (fun _ => FlowStopIdentG.measurable_histState _) _)

theorem isStrongGalmarino_aStopRule (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (c : ℝ) :
    IsStrongGalmarino (aStopRule ρL ρR c) :=
  (isStrongGalmarino_hitRuleSeq isNonAnticipating_retTimedTrace _).min
    (isStrongGalmarino_hitRuleSeq isNonAnticipating_histState _)

theorem isHistGalmarino_aStopRule (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (c : ℝ) :
    IsHistGalmarino (aStopRule ρL ρR c) :=
  (isStrongGalmarino_aStopRule ρL ρR c).isHistGalmarino

/-- **The A-stop rule reads the A-stop from the killed history.** -/
theorem aStopRule_killedHistory {Ω : Type*} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    (hWc : ∀ ω, Continuous (W · ω)) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
    {c : ℝ} {γ : ℝ≥0 → ℂ} (hW0 : W 0 ω = 0) (hg : IsGeneratingTrace (W · ω) (V ω) γ) (hV0 : 0 < V ω)
    (hthr : V ω ≤ thr ρL ρR W xL xR ω)
    (hoff : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < V ω → γ t ∉ codeJ c)
    (hend : V ω ≠ ⊤ → V ω = thr ρL ρR W xL xR ω ∨ γ (V ω).toNNReal ∈ codeJ c) :
    aStopRule ρL ρR c (killedHistory W (geomLW W xL) (geomRW W xR) V ω) = V ω := by
  set hist := killedHistory W (geomLW W xL) (geomRW W xR) V ω with hhist
  have hγ1 : hist.1 = V ω := rfl
  have hst : Continuous fun t => (W t ω, fun i => geomLW W xL i t ω, fun j => geomRW W xR j t ω) :=
    (hWc ω).prodMk ((continuous_pi fun i => (isForcePath_geomLW hWc xL ω i).1).prodMk
      (continuous_pi fun j => (isForcePath_geomRW hWc xR ω j).1))
  have hstc : ContinuousOn (fun t => (W t ω, fun i => geomLW W xL i t ω, fun j => geomRW W xR j t ω))
      {t | (t : ℝ≥0∞) < V ω} := hst.continuousOn
  have hg' : IsGeneratingTrace (fun t => W t ω) (V ω) (fun t => γ t - ((0 : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using hg
  have hψT : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < V ω →
      retTimedTrace hist (dyadicTime p) = (dyadicTime p, γ (dyadicTime p)) := fun p hp =>
    Prod.ext rfl (histTrace_killedHistory hstc hW0 hg' hp)
  have hψS : ∀ p : ℕ × ℕ, (dyadicTime p : ℝ≥0∞) < V ω → histState hist (dyadicTime p) =
      (W (dyadicTime p) ω, fun i => geomLW W xL i (dyadicTime p) ω, fun j => geomRW W xR j (dyadicTime p) ω) :=
    fun p hp => histState_killedHistory hstc hp
  have hoffT : ∀ m, ∀ s : ℝ≥0, (s : ℝ≥0∞) < V ω → (s, γ s) ∉ aStopPiece c m := by
    intro m s hs hm
    have hs0 : 0 < s := lt_of_lt_of_le (by positivity : (0 : ℝ≥0) < 1 / (m + 1)) hm.1
    exact hoff s hs0 hs hm.2
  have hoffS : ∀ m, ∀ s : ℝ≥0, (s : ℝ≥0∞) < V ω →
      (W s ω, fun i => geomLW W xL i s ω, fun j => geomRW W xR j s ω) ∉ thrSet ρL ρR m := by
    intro m s hs hm
    have h := FCPlumb.thr_le_of_force_threshold hWc (thresholdCondition_of_mem_thrSet hm)
    exact absurd (hthr.trans h) (not_le.2 hs)
  have hγc : ContinuousOn γ {t | (t : ℝ≥0∞) ≤ V ω} := hg.2.1
  have hT1 : V ω ≤ hitRuleSeq retTimedTrace (aStopPiece c) hist :=
    le_hitRuleSeq_of_off (isClosed_aStopPiece c)
      (continuous_id.continuousOn.prodMk (hγc.mono fun t (ht : (t : ℝ≥0∞) < V ω) =>
        show (t : ℝ≥0∞) ≤ V ω from ht.le)) hoffT (fun p hp _ => hψT p hp)
  have hS1 : V ω ≤ hitRuleSeq histState (thrSet ρL ρR) hist :=
    le_hitRuleSeq_of_off (isClosed_thrSet ρL ρR) hstc hoffS (fun p hp _ => hψS p hp)
  show min (hitRuleSeq retTimedTrace (aStopPiece c) hist) (hitRuleSeq histState (thrSet ρL ρR) hist) = V ω
  rcases eq_top_or_lt_top (V ω) with htop | hlt
  · rw [htop] at hT1 hS1 ⊢
    rw [top_le_iff.1 hT1, top_le_iff.1 hS1, min_self]
  · set T : ℝ≥0 := (V ω).toNNReal with hTdef
    have hT : (T : ℝ≥0∞) = V ω := ENNReal.coe_toNNReal hlt.ne
    have hTpos : 0 < T := by
      rw [← ENNReal.coe_pos, hT]
      exact hV0
    have hγT : hist.1 = T := hγ1.trans hT.symm
    have hlt' : ∀ s : ℝ≥0, s < T → (s : ℝ≥0∞) < V ω := fun s hs => hT ▸ ENNReal.coe_lt_coe.2 hs
    rcases hend hlt.ne with h | h
    · have hmem := thr_mem_thresholdSet (ρL := ρL) (ρR := ρR) hWc xL xR (T := T) (hT.trans h).symm
      obtain ⟨m₀, hm₀⟩ := exists_mem_thrSet (ρL := ρL) (ρR := ρR)
        (s := (W T ω, fun i => geomLW W xL i T ω, fun j => geomRW W xR j T ω)) hmem
      have hS : hitRuleSeq histState (thrSet ρL ρR) hist = T :=
        hitRuleSeq_eq_of_hit (isClosed_thrSet ρL ρR) hTpos hγT hst.continuousOn
          (fun m s hs => hoffS m s (hlt' s hs)) hm₀ (fun p hp => hψS p (hT ▸ hp))
      rw [hS, hT, min_eq_right hT1]
    · obtain ⟨m, hm⟩ := exists_nat_one_div_lt (NNReal.coe_pos.2 hTpos)
      have hmem : (T, γ T) ∈ aStopPiece c m := ⟨by exact_mod_cast hm.le, h⟩
      have hTc : ContinuousOn (fun t => (t, γ t)) (Iic T) :=
        continuous_id.continuousOn.prodMk (hγc.mono fun t (ht : t ≤ T) =>
          show (t : ℝ≥0∞) ≤ V ω from hT ▸ ENNReal.coe_le_coe.2 ht)
      have hE : hitRuleSeq retTimedTrace (aStopPiece c) hist = T :=
        hitRuleSeq_eq_of_hit (isClosed_aStopPiece c) hTpos hγT hTc
          (fun m s hs => hoffT m s (hlt' s hs)) hmem (fun p hp => hψT p (hT ▸ hp))
      rw [hE, hT, min_eq_left hS1]

/-- **A model with an initial code whose lifetime is a Galmarino rule of its killed history, given the code**
(the R79-safe form for models with codes). -/
def HasCodeHistoryRule {κ θ : ℝ} (M : StoppedTypeModelJ κ θ) : Prop :=
  ∃ R : ℝ → HistorySpace M.data.nL M.data.nR → ℝ≥0∞, (∀ c, Measurable (R c)) ∧ (∀ c, IsHistGalmarino (R c)) ∧
    ∀ᵐ ω ∂M.law, M.data.life ω = R (M.data.code ω) (killedHistory M.data.driver
      (geomLW M.data.driver M.data.xL) (geomRW M.data.driver M.data.xR) M.data.life ω)

end InteractingSLE.RLC.OrdModel
