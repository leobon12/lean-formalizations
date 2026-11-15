/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.AssemblyUnique
import InteractingSLE.Spec.Exist.StagedDet

/-!
# Theorem 2.2's solution relation is jointly measurable in the word

Packet PROVE-PARAM12B. Theorem 2.2's assembly (`Sec2.Assembly`) encodes a solution of Definition 2.1 by its dyadic
values (`XCode`) and shows that, for each fixed force word, the canonical solution codes `CRel a xL xR ρL ρR` form a
measurable set (`measurableSet_cRel`). A coupling law measurable in the word (`Param12Limit`) needs the same with the
word as a parameter: the set of pairs (word data, code) with the code a canonical solution code of that word is a
measurable subset of `WordData nL nR × XCode nL nR`.

The per-word proof already reduces the frozen predicate, on good codes with the threshold limit, to countably many
conditions (`isIntegratedSLEPath_iff_mem_mSet`). Each of them is jointly measurable: the word enters through the
initial values, linearly through the weights in the integrated drifts (`∫ ρ/(w − v) = ρ ∫ 1/(w − v)`), through the
weight sums of the dyadic threshold conditions, and through the threshold condition at time `0` and at the lifetime
(`measurable_thresholdCondition`).

## Main results

* `measurable_thresholdCondition`: the threshold condition is jointly measurable in weights, driver and marks;
* `measurableSet_paramRel`, **`measurableSet_paramCRel`**: `{(w, x) | x ∈ Rel a w}` and `{(w, x) | x ∈ CRel a w}`
  are measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace Param12

open Sec2.Assembly Staged

variable {nL nR : ℕ}

/-! ### The threshold condition -/

/-- **The threshold condition is jointly measurable** in the weights, the driver and the marks. -/
theorem measurable_thresholdCondition {α : Type*} [MeasurableSpace α] {ρL : α → Fin nL → ℝ}
    {ρR : α → Fin nR → ℝ} {w : α → ℝ} {vL : α → Fin nL → ℝ} {vR : α → Fin nR → ℝ} (hρL : Measurable ρL)
    (hρR : Measurable ρR) (hw : Measurable w) (hvL : Measurable vL) (hvR : Measurable vR) :
    Measurable fun p => ForceWord.ThresholdCondition (ρL p) (ρR p) (w p) (vL p) (vR p) := by
  unfold ForceWord.ThresholdCondition
  simp only [Finset.sum_filter]
  have hL : Measurable fun p => ∑ i, if vL p i = w p then ρL p i else 0 :=
    Finset.measurable_sum _ fun i _ => Measurable.ite
      (measurableSet_eq_fun ((measurable_pi_apply i).comp hvL) hw) ((measurable_pi_apply i).comp hρL)
      measurable_const
  have hR : Measurable fun p => ∑ j, if vR p j = w p then ρR p j else 0 :=
    Finset.measurable_sum _ fun j _ => Measurable.ite
      (measurableSet_eq_fun ((measurable_pi_apply j).comp hvR) hw) ((measurable_pi_apply j).comp hρR)
      measurable_const
  exact (measurableSet_setOfPred.1 (measurableSet_le hL measurable_const)).or
    (measurableSet_setOfPred.1 (measurableSet_le hR measurable_const))

/-! ### The coordinates of a pair (word data, code) -/

section Coord

theorem measurable_wxL : Measurable fun p : WordData nL nR × XCode nL nR => p.1.1.1 :=
  measurable_fst.comp (measurable_fst.comp measurable_fst)
theorem measurable_wxR : Measurable fun p : WordData nL nR × XCode nL nR => p.1.1.2 :=
  measurable_snd.comp (measurable_fst.comp measurable_fst)
theorem measurable_wρL : Measurable fun p : WordData nL nR × XCode nL nR => p.1.2.1 :=
  measurable_fst.comp (measurable_snd.comp measurable_fst)
theorem measurable_wρR : Measurable fun p : WordData nL nR × XCode nL nR => p.1.2.2 :=
  measurable_snd.comp (measurable_snd.comp measurable_fst)

end Coord

/-! ### The countable conditions, with the word as a parameter -/

/-- The integrated drift of the driver, with the weights taken out of the integrals. -/
theorem defect_eq (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (x : XCode nL nR) (t : ℝ≥0) :
    defect a xL xR ρL ρR x t =
      (cw x t - (Real.sqrt a * cb x t
          + (∑ i, ρL i * ∫ s in (0 : ℝ)..t, (cw x s.toNNReal - cvL x i s.toNNReal)⁻¹)
          + (∑ j, ρR j * ∫ s in (0 : ℝ)..t, (cw x s.toNNReal - cvR x j s.toNNReal)⁻¹)),
        fun i => cvL x i t - (xL i + ∫ s in (0 : ℝ)..t, 2 / (cvL x i s.toNNReal - cw x s.toNNReal)),
        fun j => cvR x j t - (xR j + ∫ s in (0 : ℝ)..t, 2 / (cvR x j s.toNNReal - cw x s.toNNReal))) := by
  simp only [defect, div_eq_mul_inv, intervalIntegral.integral_const_mul]

theorem measurable_paramDefect (a : ℝ) (t : ℝ≥0) :
    Measurable fun p : WordData nL nR × XCode nL nR => defect a p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2 p.2 t := by
  simp only [defect_eq]
  have hL : ∀ i, Measurable fun x : XCode nL nR => ∫ s in (0 : ℝ)..t, (cw x s.toNNReal - cvL x i s.toNNReal)⁻¹ :=
    fun i => measurable_intervalIntegral (g := fun x s => (cw x s.toNNReal - cvL x i s.toNNReal)⁻¹)
      (measurable_cw_real.sub (measurable_cvL_real i)).inv t
  have hR : ∀ j, Measurable fun x : XCode nL nR => ∫ s in (0 : ℝ)..t, (cw x s.toNNReal - cvR x j s.toNNReal)⁻¹ :=
    fun j => measurable_intervalIntegral (g := fun x s => (cw x s.toNNReal - cvR x j s.toNNReal)⁻¹)
      (measurable_cw_real.sub (measurable_cvR_real j)).inv t
  have fL : ∀ i, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, 2 / (cvL x i s.toNNReal - cw x s.toNNReal) := fun i =>
    measurable_intervalIntegral (g := fun x s => 2 / (cvL x i s.toNNReal - cw x s.toNNReal))
      (measurable_const.div ((measurable_cvL_real i).sub measurable_cw_real)) t
  have fR : ∀ j, Measurable fun x : XCode nL nR =>
      ∫ s in (0 : ℝ)..t, 2 / (cvR x j s.toNNReal - cw x s.toNNReal) := fun j =>
    measurable_intervalIntegral (g := fun x s => 2 / (cvR x j s.toNNReal - cw x s.toNNReal))
      (measurable_const.div ((measurable_cvR_real j).sub measurable_cw_real)) t
  have hs : Measurable (Prod.snd : WordData nL nR × XCode nL nR → XCode nL nR) := measurable_snd
  refine (((measurable_cw_at t).comp hs).sub (((measurable_const.mul ((measurable_cb_at t).comp hs)).add
    (Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp measurable_wρL).mul ((hL i).comp hs))).add
    (Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp measurable_wρR).mul ((hR j).comp hs)))).prodMk
    ((measurable_pi_iff.2 fun i => ((measurable_cvL_at i t).comp hs).sub
      (((measurable_pi_apply i).comp measurable_wxL).add ((fL i).comp hs))).prodMk
    (measurable_pi_iff.2 fun j => ((measurable_cvR_at j t).comp hs).sub
      (((measurable_pi_apply j).comp measurable_wxR).add ((fR j).comp hs))))

theorem measurable_paramNThr :
    Measurable fun p : WordData nL nR × XCode nL nR => NThr p.1.2.1 p.1.2.2 p.2 := by
  have hs : Measurable (Prod.snd : WordData nL nR × XCode nL nR → XCode nL nR) := measurable_snd
  unfold NThr
  refine Measurable.forall fun n₀ => Measurable.forall fun k₀ =>
    ((measurable_coe_lt _ measurable_cζ).comp hs).imp (Measurable.and ?_ ?_)
  · refine Measurable.forall fun S => Measurable.imp ?_ (Measurable.not ?_)
    · exact measurableSet_setOfPred.1 (measurableSet_le (Finset.measurable_sum _ fun i _ =>
        (measurable_pi_apply i).comp measurable_wρL) measurable_const)
    · refine Measurable.exists fun p => Measurable.forall fun m => Measurable.exists fun n =>
        Measurable.exists fun k => measurable_const.and ?_
      exact (measurable_nearSide S p m (measurable_cw_at _) fun i => measurable_cvL_at i _).comp hs
  · refine Measurable.forall fun S => Measurable.imp ?_ (Measurable.not ?_)
    · exact measurableSet_setOfPred.1 (measurableSet_le (Finset.measurable_sum _ fun j _ =>
        (measurable_pi_apply j).comp measurable_wρR) measurable_const)
    · refine Measurable.exists fun p => Measurable.forall fun m => Measurable.exists fun n =>
        Measurable.exists fun k => measurable_const.and ?_
      exact (measurable_nearSide S p m (measurable_cw_at _) fun j => measurable_cvR_at j _).comp hs

/-- **The countable conditions are jointly measurable** in the word data and the code. -/
theorem measurableSet_paramMSet (a : ℝ) :
    MeasurableSet {p : WordData nL nR × XCode nL nR | p.2 ∈ MSet a p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2} := by
  have hs : Measurable (Prod.snd : WordData nL nR × XCode nL nR → XCode nL nR) := measurable_snd
  refine measurableSet_setOfPred.2 ?_
  unfold MSet
  simp only [mem_ofPred_eq]
  refine Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_
    (Measurable.and ?_ (Measurable.and ?_ (Measurable.and ?_ ?_))))))
  · exact (measurable_eq_real ((measurable_cw_at 0).comp hs) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real ((measurable_cvL_at i 0).comp hs)
        ((measurable_pi_apply i).comp measurable_wxL)).and
        (Measurable.forall fun j => measurable_eq_real ((measurable_cvR_at j 0).comp hs)
          ((measurable_pi_apply j).comp measurable_wxR)))
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      (((measurable_coe_lt _ measurable_cζ).imp
        (measurableSet_setOfPred.1 (measurable_stateAt _ isClosed_ordSet.measurableSet))).comp hs)
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      ((measurable_coe_lt _ measurable_cζ).imp (measurable_intAt _)).comp hs
  · exact Measurable.forall fun n => Measurable.forall fun k =>
      ((measurable_coe_lt _ measurable_cζ).comp hs).imp
        (measurableSet_setOfPred.1 (measurable_paramDefect a _ (measurableSet_singleton 0)))
  · exact Measurable.forall fun i =>
      (measurable_collision measurable_cw_real (measurable_cvL_real i)).comp hs
  · exact Measurable.forall fun j =>
      (measurable_collision measurable_cw_real (measurable_cvR_real j)).comp hs
  · exact measurable_paramNThr
  · exact ((measurableSet_setOfPred.1 (measurable_cζ (measurableSet_singleton 0))).comp hs).imp
      (measurable_thresholdCondition measurable_wρL measurable_wρR measurable_const measurable_wxL
        measurable_wxR)

theorem measurable_paramLimThr :
    Measurable fun p : WordData nL nR × XCode nL nR => LimThr p.1.2.1 p.1.2.2 p.2 := by
  have hs : Measurable (Prod.snd : WordData nL nR × XCode nL nR → XCode nL nR) := measurable_snd
  have hlim := (measurable_limState (nL := nL) (nR := nR)).comp hs
  unfold LimThr
  exact ((measurableSet_setOfPred.1 (measurableSet_lt measurable_const measurable_cζ)).comp hs).imp
    (((measurableSet_setOfPred.1 (measurableSet_lt measurable_cζ measurable_const)).comp hs).imp
      (measurable_thresholdCondition measurable_wρL measurable_wρR hlim.fst hlim.snd.fst hlim.snd.snd))

/-! ### The solution relation and the canonical solution codes -/

/-- **Theorem 2.2's solution relation is jointly measurable in the word data and the code.** -/
theorem measurableSet_paramRel (a : ℝ) :
    MeasurableSet {p : WordData nL nR × XCode nL nR | p.2 ∈ Rel a p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2} := by
  have e : {p : WordData nL nR × XCode nL nR | p.2 ∈ Rel a p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2} =
      ({p : WordData nL nR × XCode nL nR | Good p.2} ∩ {p | LimThr p.1.2.1 p.1.2.2 p.2}) ∩
        {p | p.2 ∈ MSet a p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2} := by
    ext p
    exact ⟨fun ⟨hg, hl, hp⟩ => ⟨⟨hg, hl⟩, (isIntegratedSLEPath_iff_mem_mSet hg hl).1 hp⟩,
      fun ⟨⟨hg, hl⟩, hm⟩ => ⟨hg, hl, (isIntegratedSLEPath_iff_mem_mSet hg hl).2 hm⟩⟩
  rw [e]
  exact ((measurableSet_good.preimage measurable_snd).inter
    (measurableSet_setOfPred.2 measurable_paramLimThr)).inter (measurableSet_paramMSet a)

theorem measurable_paramCanon :
    Measurable fun p : WordData nL nR × XCode nL nR => Canon p.1.1.1 p.1.1.2 p.2 := by
  have hs : Measurable (Prod.snd : WordData nL nR × XCode nL nR → XCode nL nR) := measurable_snd
  have hw : ∀ n k, Measurable fun p : WordData nL nR × XCode nL nR => p.2.2.2.1 n k := fun n k =>
    ((measurable_code n k).comp measurable_code_w).comp hs
  have hL : ∀ i n k, Measurable fun p : WordData nL nR × XCode nL nR => p.2.2.2.2.1 i n k := fun i n k =>
    ((measurable_code n k).comp (measurable_code_vL i)).comp hs
  have hR : ∀ j n k, Measurable fun p : WordData nL nR × XCode nL nR => p.2.2.2.2.2 j n k := fun j n k =>
    ((measurable_code n k).comp (measurable_code_vR j)).comp hs
  unfold Canon
  refine Measurable.forall fun n => Measurable.forall fun k => Measurable.and ?_ ?_
  · exact measurable_const_imp _ ((measurable_eq_real (hw n k) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (hL i n k) ((measurable_pi_apply i).comp measurable_wxL)).and
        (Measurable.forall fun j => measurable_eq_real (hR j n k) ((measurable_pi_apply j).comp measurable_wxR))))
  · exact measurable_const_imp _ (((measurable_coe_lt _ measurable_cζ).comp hs).not.imp
      ((measurable_eq_real (hw n k) measurable_const).and
      ((Measurable.forall fun i => measurable_eq_real (hL i n k) measurable_const).and
        (Measurable.forall fun j => measurable_eq_real (hR j n k) measurable_const))))

/-- **The canonical solution codes are jointly measurable in the word data and the code.** -/
theorem measurableSet_paramCRel (a : ℝ) :
    MeasurableSet {p : WordData nL nR × XCode nL nR | p.2 ∈ CRel a p.1.1.1 p.1.1.2 p.1.2.1 p.1.2.2} :=
  (measurableSet_paramRel a).inter (measurableSet_setOfPred.2 measurable_paramCanon)

end Param12

end Exist

end InteractingSLE
