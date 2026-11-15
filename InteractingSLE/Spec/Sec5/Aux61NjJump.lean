/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CmpCfGerm
import InteractingSLE.Spec.Sec5.Aux61KernelTop
import InteractingSLE.Spec.Sec7.Prop74ProofWord
import InteractingSLE.Spec.Sec7.Lemma71BStop

/-!
# The returned counterflow word has no jump on the eastern side

Packet PROVE-AUX61-NOJUMP (ruling R103: "the capture's landing coordinate is not a jump of the
returned boundary word"). For the source's flow line the force word is the seed word of
`prop74Data a b` from `0` (marks `0⁻`, `0⁺` only), so the dual counterflow word has its two marks at
its own seed, and at the retained time `s` these sit at the images `g_s(0∓) − w_s` of the two sides
of the counterflow base. In the counterflow chart `Ψ_s` the returned word therefore jumps only at
`0`, at `junR = −1/(g_s(0⁻) − w_s) ≥ 0` and at `−1/(g_s(0⁺) − w_s) ≤ 0`:

* `forall_mem_forceJumpFinset_source`, `forall_mem_counterflowJumps_source`: every mark is `0`;
* `cfPosL_source`, `cfPosR_source`: the two returned positions;
* **`le_junR_of_mem_returnedCfJumps`**: every returned jump is `≤ junR (cfW S p) s`, at **every**
  sample (deterministic);
* **`notMem_returnedCfJumps_east`**: every counterflow-chart point right of the junction is a regular point
  of the returned word (every sample; no gap hypothesis — compare `Aux61Cpt.notMem_returnedCfJumps_of_junR_lt`,
  PROVE-AUX61-CAPTURE, which assumes a strict left base gap).

The exact returned positions `cfPosL_source`, `cfPosR_source` also give the eastern returned value
(`Aux61NjHeight`).

R48: no Theorem 1.2/1.3 input; R77: no post-contact kernel. Nothing here replaces a source statement.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open QuantumZipper (H chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61Nj
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign LawUnique GlueCond WangWu Cond44Ref Aux61GWord
open Aux61Cmp Sec7.StripSysField CrossCond.Word49 Aux61Kernel
universe u

/-! ### Force words whose marks are all at the seed -/

theorem flowLineXL_eq_zero_of_forall {b : ℝ → ℝ} {J : Finset ℝ} (hJ : ∀ y ∈ J, y = 0)
    (i : Fin (flowLineNL b J 0)) : flowLineXL b J 0 i = 0 := by
  revert i
  unfold flowLineXL flowLineNL
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Fin.cons_zero _ _
  · exfalso
    have hmem := Finset.orderEmbOfFin_mem
      ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < 0)) rfl (Fin.rev j)
    rw [Finset.mem_filter] at hmem
    have h0 := hJ _ (Finset.mem_filter.1 hmem.1).1
    linarith [hmem.2]

theorem flowLineXR_eq_zero_of_forall {b : ℝ → ℝ} {J : Finset ℝ} (hJ : ∀ y ∈ J, y = 0)
    (i : Fin (flowLineNR b J 0)) : flowLineXR b J 0 i = 0 := by
  revert i
  unfold flowLineXR flowLineNR
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact Fin.cons_zero _ _
  · exfalso
    have hmem := Finset.orderEmbOfFin_mem
      ((PiecewiseConstantBoundaryData.jumpSet b J).filter (0 < ·)) rfl j
    rw [Finset.mem_filter] at hmem
    have h0 := hJ _ (Finset.mem_filter.1 hmem.1).1
    linarith [hmem.2]

/-- The marks of the source's force word are all at its seed. -/
theorem forall_mem_forceJumpFinset_source (S : SourceSetting.{u}) :
    ∀ y ∈ forceJumpFinset S.xL S.xR, y = 0 := by
  intro y hy
  simp only [forceJumpFinset, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hy
  rcases hy with rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rfl
  · exact Sec7.flowLineXL_prop74Data S.a S.b j
  · exact Sec7.flowLineXR_prop74Data S.a S.b j

theorem forall_mem_counterflowJumps {J : Finset ℝ} (hJ : ∀ y ∈ J, y = 0) :
    ∀ y ∈ counterflowJumps J, y = 0 := by
  intro y hy
  simp only [counterflowJumps, returnExcept, Finset.mem_insert, Finset.mem_image] at hy
  rcases hy with rfl | ⟨v, hv, rfl⟩
  · rfl
  · rw [hJ v hv, inv_zero, neg_zero]

theorem forall_mem_counterflowJumps_source (S : SourceSetting.{u}) :
    ∀ y ∈ counterflowJumps (forceJumpFinset S.xL S.xR), y = 0 :=
  forall_mem_counterflowJumps (forall_mem_forceJumpFinset_source S)

/-- The left returned position: the image of `0⁻`. -/
theorem cfPosL_source (S : SourceSetting.{u}) (w : ℝ≥0 → ℝ) (t : ℝ≥0)
    (i : Fin (flowLineNL (counterflowData S.κ (sourceCounterBoundary S))
      (counterflowJumps (forceJumpFinset S.xL S.xR)) 0)) :
    cfPosL S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR) w t i =
      -MartChar.RealFlow.rightImg (fun s => -Ito.rpath w s) 0 t - w t := by
  rw [cfPosL, flowLineXL_eq_zero_of_forall (forall_mem_counterflowJumps_source S) i, neg_zero]

/-- The right returned position: the image of `0⁺`. -/
theorem cfPosR_source (S : SourceSetting.{u}) (w : ℝ≥0 → ℝ) (t : ℝ≥0)
    (i : Fin (flowLineNR (counterflowData S.κ (sourceCounterBoundary S))
      (counterflowJumps (forceJumpFinset S.xL S.xR)) 0)) :
    cfPosR S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR) w t i =
      MartChar.RealFlow.rightImg (Ito.rpath w) 0 t - w t := by
  rw [cfPosR, flowLineXR_eq_zero_of_forall (forall_mem_counterflowJumps_source S) i]

/-! ### The returned jumps lie left of the junction -/

theorem rpath_coe (w : ℝ≥0 → ℝ) (t : ℝ≥0) : Ito.rpath w (t : ℝ) = w t := by
  simp only [Ito.rpath, Real.toNNReal_coe]

/-- **Every returned jump is at most the junction `junR`** (every sample). -/
theorem le_junR_of_mem_returnedCfJumps (S : SourceSetting.{u}) (p : S.Ω × HistorySpace 0 0)
    {x : ℝ} (hx : x ∈ returnedCfJumps S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
      (rationalTime S.s) p.2) :
    x ≤ junR (cfW S p) (rationalTime S.s) := by
  have hw : Continuous (cfW S p) := Sec4.continuous_rpath_regPath _
  have hs : (0 : ℝ) ≤ (rationalTime S.s : ℝ) := NNReal.coe_nonneg _
  have hjun : 0 ≤ junR (cfW S p) (rationalTime S.s) := junR_nonneg hw hs
  rw [returnedCfJumps, returnExcept, Finset.mem_insert, Finset.mem_image] at hx
  rcases hx with rfl | ⟨v, hv, rfl⟩
  · exact hjun
  · rw [forceJumpFinset, Finset.mem_insert, Finset.mem_union, Finset.mem_image,
      Finset.mem_image] at hv
    rcases hv with rfl | ⟨i, -, rfl⟩ | ⟨i, -, rfl⟩
    · rw [inv_zero, neg_zero]
      exact hjun
    · rw [cfPosL_source]
      refine le_of_eq ?_
      rw [junR, neg_div, one_div]
      simp only [cfW, rpath_coe]
    · rw [cfPosR_source]
      have hle : Sec4.regPath (cfStop (rationalTime S.s) p.2) (rationalTime S.s) ≤
          MartChar.RealFlow.rightImg (Ito.rpath (Sec4.regPath (cfStop (rationalTime S.s) p.2))) 0
            (rationalTime S.s) := by
        have h := MartChar.RealFlow.le_rightImg hw 0 hs
        simpa only [cfW, rpath_coe] using h
      have h0 : -(MartChar.RealFlow.rightImg (Ito.rpath (Sec4.regPath (cfStop (rationalTime S.s) p.2)))
          0 (rationalTime S.s) - Sec4.regPath (cfStop (rationalTime S.s) p.2) (rationalTime S.s))⁻¹ ≤ 0 :=
        neg_nonpos.2 (inv_nonneg.2 (sub_nonneg.2 hle))
      exact h0.trans hjun

/-- **Points right of the junction are regular points of the returned word** (every sample). -/
theorem notMem_returnedCfJumps_east (S : SourceSetting.{u}) (p : S.Ω × HistorySpace 0 0)
    {x : ℝ} (hx : junR (cfW S p) (rationalTime S.s) < x) :
    x ∉ returnedCfJumps S.κ (sourceCounterBoundary S) (forceJumpFinset S.xL S.xR)
      (rationalTime S.s) p.2 := fun h =>
  absurd (le_junR_of_mem_returnedCfJumps S p h) (not_le.2 hx)

end InteractingSLE.Sec5.Aux61Nj
