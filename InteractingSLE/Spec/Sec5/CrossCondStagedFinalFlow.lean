/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSideHeightProbSide
import InteractingSLE.Spec.Sec5.CrossCondStagedLawSide

/-!
# The staged cross-conditioning law: the record positions of the born marks

Packet PROVE-CROSSCOND-STAGED4 (S2). The stop word of a piece (`Exist.StagedLaw.stopWord`) places its marks at the
record positions `markPos`/`markPosL` of the marks of the word before the piece, read from the piece's record driver.
For a staged prefix (one concatenated driver `V`, the pieces starting at the switch times `a`), the marks created at the
switches are the base images of the shifted chain, `chartAL (shiftDrive V a) (t − a)`, `chartAR (shiftDrive V a)
(t − a)` (the born marks of PROVE-CROSSCOND-STAGED3's `IsBornPairL/R`). This file proves the two real-flow facts that
make the record positions of the iterated stop words these base images:

* **`markPos_zero_eq`**: the record position of `0⁺` is the geometric image of `0⁺`: `markPos w T 0 = R_T − W_T`
  (`= chartAR w T`; the landed `rightImg_sub_le_markPos` is one inequality; the other is the infimum over the alive
  rationals and the `1`-Lipschitz real flow); `markPosL_zero_eq` (`= chartAL w T`) by reflection;
* **`markPos_shiftDrive_chartAR`** (the flow property of the base images): if the right base image of `V` stays right
  of the driver on `[s, s + U]` (`s > 0`), the record position of `chartAR V s` read from the shifted driver
  `shiftDrive V s` at time `U` is `chartAR V (s + U)` (the base image moves by the Loewner equation away from the
  driver,
  `rightImg_eq_add_integral`, so it is a mark, and `markPos_eq` reads it); `markPosL_shiftDrive_chartAL` by reflection.

Deterministic. Conditional helpers with distinct names; R48: no Theorem 1.2/1.3 input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open QuantumZipper (H fwdMap)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Sec5.CrossCond.StagedFinal

open Exist.StagedLaw MartChar.RealFlow Sec7.StripSideHeightProb
open WangWu (chartAL chartAR)

/-! ### The record position of the seed -/

section Seed

variable {w : ℝ → ℝ} {T : ℝ}

/-- **The record position of `0⁺` is the geometric image of `0⁺`**: `markPos w T 0 = R_T − W_T`. -/
theorem markPos_zero_eq (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) :
    markPos w T 0 = rightImg w 0 T - w T := by
  classical
  refine le_antisymm ?_ (rightImg_sub_le_markPos hw hw0 hT)
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  obtain ⟨y, hy0, hyA, hyg⟩ := exists_lt_of_rightImg_lt hw hT
    (show rightImg w 0 T < rightImg w 0 T + ε / 2 by linarith)
  obtain ⟨q, hyq, hqy⟩ := exists_rat_btwn (show y < y + ε / 2 by linarith)
  have hqA : Alive w q T := hyA.of_le hw hyq.le hT
  have hlip := abs_gImg_sub_le hw hT hyA hqA
  rw [abs_of_pos (by linarith : (0 : ℝ) < q - y)] at hlip
  have hgq : gImg w q T < rightImg w 0 T + ε := by
    have := (abs_le.1 hlip).2
    linarith
  have hu' := WangWu.isForwardSol_of_alive hw hqA
  have hf := fwdMap_eq_of_isForwardSol hw hu' ⟨hT, le_rfl⟩
  have hterm : markTerm w T 0 q = (((fwdMap w T ((q : ℝ) : ℂ)).re : ℝ) : EReal) := by
    unfold markTerm
    exact ite_eq_left_of_eq_true _ _ (eq_true ⟨by exact_mod_cast hy0.trans hyq, _, hu'⟩)
  have hre : (fwdMap w T ((q : ℝ) : ℂ)).re = gImg w q T - w T := by
    rw [hf]
    simp only [gImg]
    simp
  have hle : (⨅ q' : ℚ, markTerm w T 0 q') ≤ (((gImg w q T - w T : ℝ)) : EReal) := by
    rw [← hre, ← hterm]
    exact iInf_le _ q
  have hbot : (⨅ q' : ℚ, markTerm w T 0 q') ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) (zero_le_iInf_markTerm hw hw0 hT le_rfl)
  have h1 : markPos w T 0 ≤ gImg w q T - w T := by
    unfold markPos
    have := EReal.toReal_le_toReal hle hbot (EReal.coe_ne_top _)
    rwa [EReal.toReal_coe] at this
  linarith

/-- The record position of `0⁺` is `chartAR w T`. -/
theorem markPos_zero_eq_chartAR (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) :
    markPos w T 0 = chartAR w T :=
  markPos_zero_eq hw hw0 hT

/-- **The record position of `0⁻` is the geometric image of `0⁻`**: `markPosL w T 0 = chartAL w T`. -/
theorem markPosL_zero_eq_chartAL (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) :
    markPosL w T 0 = chartAL w T := by
  have h := markPos_zero_eq (w := fun s => -w s) hw.neg (by simp [hw0]) hT
  unfold markPosL chartAL
  rw [neg_zero, h]
  ring

end Seed

/-! ### The flow property of the base images -/

section Flow

variable {V : ℝ → ℝ}

theorem shiftDrive_neg (V : ℝ → ℝ) (s : ℝ) : shiftDrive (fun r => -V r) s = fun r => -shiftDrive V s r := by
  funext r
  simp only [shiftDrive]
  ring

theorem chartAR_neg (V : ℝ → ℝ) (s : ℝ) : chartAR (fun r => -V r) s = -chartAL V s := by
  unfold chartAR chartAL
  ring

/-- **The flow property of the right base image.** If the right base image of `V` stays strictly right of the driver
on `[s, s + U]` (`0 < s`), the record position of `chartAR V s` read from `shiftDrive V s` at time `U` is
`chartAR V (s + U)`. -/
theorem markPos_shiftDrive_chartAR (hV : Continuous V) {s U : ℝ} (hs : 0 < s) (hU : 0 ≤ U)
    (hgap : ∀ r ∈ Icc s (s + U), 0 < chartAR V r) :
    markPos (shiftDrive V s) U (chartAR V s) = chartAR V (s + U) := by
  have hw := QuantumZipper.RS.continuous_shiftDrive hV s
  have hw0 : shiftDrive V s 0 = 0 := by simp only [shiftDrive, add_zero, sub_self]
  -- the gap is bounded below on the window
  have hRc : ContinuousOn (fun r => chartAR V r) (Icc s (s + U)) := by
    have h1 := (continuousOn_rightImg hV 0).mono (fun r (hr : r ∈ Icc s (s + U)) =>
      (show r ∈ Ici (0 : ℝ) from hs.le.trans hr.1))
    exact h1.sub hV.continuousOn
  obtain ⟨r₀, hr₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (by linarith)) hRc
  set c := chartAR V r₀ / 2 with hc
  have hc0 : 0 < c := by have := hgap r₀ hr₀; rw [hc]; linarith
  have hgap' : ∀ u ∈ Icc s (s + U), c < rightImg V 0 u - V u := fun u hu => by
    have h1 : chartAR V r₀ ≤ chartAR V u := hmin hu
    have h2 := hgap r₀ hr₀
    change c < chartAR V u
    rw [hc]
    linarith
  set d : ℝ → ℝ := fun r => chartAR V (s + r) with hd
  have hdpos : ∀ r ∈ Icc (0 : ℝ) U, c < d r := fun r hr => hgap' (s + r) ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hdc : ContinuousOn d (Icc 0 U) := by
    refine hRc.comp (continuous_const.add continuous_id).continuousOn fun r hr => ?_
    exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hinv : ContinuousOn (fun r => 2 / d r) (Icc 0 U) :=
    continuousOn_const.div hdc fun r hr => (hc0.trans (hdpos r hr)).ne'
  have hint : IntervalIntegrable (fun r => 2 / d r) volume 0 U :=
    (hinv.mono (by rw [uIcc_of_le hU])).intervalIntegrable
  have hmark : IsMark (shiftDrive V s) U (chartAR V s) d := by
    refine ⟨fun r hr => (hc0.trans (hdpos r hr)).le, fun r hr => ?_, hint, ?_⟩
    · have heq := rightImg_eq_add_integral hV hs (show s ≤ s + U by linarith) hc0 hgap'
        (u := s + r) ⟨by linarith [hr.1], by linarith [hr.2]⟩
      have hsub : (∫ u in s..s + r, 2 / (rightImg V 0 u - V u)) = ∫ u in (0 : ℝ)..r, 2 / d u := by
        have := intervalIntegral.integral_comp_add_left (fun u => 2 / (rightImg V 0 u - V u)) s
          (a := (0 : ℝ)) (b := r)
        rw [add_zero] at this
        rw [← this]
        rfl
      change rightImg V 0 (s + r) - V (s + r) = (rightImg V 0 s - V s) - (V (s + r) - V s) + _
      rw [heq, hsub]
      ring
    · have hempty : {r | r ∈ Icc (0 : ℝ) U ∧ d r = 0} = ∅ := by
        ext r
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact fun hr h0 => by linarith [hdpos r hr]
      rw [hempty, measure_empty]
  rw [markPos_eq hw hw0 hU hmark]

/-- **The flow property of the left base image** (reflection of `markPos_shiftDrive_chartAR`). -/
theorem markPosL_shiftDrive_chartAL (hV : Continuous V) {s U : ℝ} (hs : 0 < s) (hU : 0 ≤ U)
    (hgap : ∀ r ∈ Icc s (s + U), chartAL V r < 0) :
    markPosL (shiftDrive V s) U (chartAL V s) = chartAL V (s + U) := by
  have hgap' : ∀ r ∈ Icc s (s + U), 0 < chartAR (fun r => -V r) r := fun r hr => by
    rw [chartAR_neg]; linarith [hgap r hr]
  have h := markPos_shiftDrive_chartAR (V := fun r => -V r) hV.neg hs hU hgap'
  unfold markPosL
  rw [← shiftDrive_neg, ← chartAR_neg, h, chartAR_neg]
  ring

end Flow

end InteractingSLE.Sec5.CrossCond.StagedFinal
