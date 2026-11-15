/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2WxMap
import InteractingSLE.Spec.Supplement.GW2SdyCut
import InteractingSLE.Spec.Supplement.GW2SdfFrame
import InteractingSLE.Spec.Supplement.GW2RootL6Drift

/-!
# The slow shell of GW2: the drift clause against `sourceDriftBound` fails; presented shells are ordered

PROVE-GW2-ROOTX round 5 (orchestrator: the `shell` field of `VPairInputsXCS` at every root, the shell's marks and
angles from GEOM2's word map). SDE's slow words (`GW2Sdx.FrameNSlowWordN`) ask the shell's angle words
`angleWordL/R κ φ m ρ₀` to PRESENT the slow stage word (`GW2Sdf.PresentsO`, which is exact: positions and weights
are the word's flow-line positions and weights). The totals of a presented word are fixed by its two far heights
(SDE's `GW2Sdw.totals_eq_of_presentsO`), and the angle blocks telescope. So the shell's far block has a total, and
hence a drift constant, bounded BELOW independently of the history (review N6, DECISIONS-FABLE-2 §F1):

* `sum_angleWordL`, `sum_angleWordR`: the angle words' totals telescope to `∓(χ/λ)(φ 0 − φ m)`;
* `totals_of_presentsO`, **`sum_far_of_presentsO`**: the far block of a presented shell sums to
  `(h_R − h_L)/λ − 2 − (χ/λ)(φ_{mL} − φ_{mR+1})`;
* **`le_stageDriftBound_of_presentsO`**: with separated angles,
  `stageDriftBound ≥ 8M/3 + (4/3)(|(h_R − h_L)/λ − 2| − M)`;
* **`le_stageDriftBound_schedWordMapX`**: for GEOM2's stage words (far heights `∓(λ′ − πχ)`, shifted by `θχ`),
  `stageDriftBound ≥ 8M/3 + (4/3)(4 − κ)`;
* `sourceDriftBound_of_zero`: for the zero boundary datum J32's drift constant is `8M/3 + 8/3`;
* **`not_shellFactLe_sourceDriftBound`**: for `κ < 2` and the zero datum NO shell presenting a stage word of GEOM2's
  map satisfies `ShellFactLe κ (sourceDriftBound c r)`. The `shell` field of `VPairInputsXCS` is therefore false for
  the shells its `words` field asks for (handoff: corrected statement, a deterministic `C*`);
* **`isOrderedForceWord_of_presentsO`**: the frame positions of any presentation are an ordered force word (the
  middle clause of `startsU`), in both orientations.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset Filter Topology
open scoped NNReal BigOperators
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Rw

open Restart Exist.Staged Exist.StagedLaw GW2Sde GW2Sdf GW2Sdy GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootL6 GW2TipStage GW2Wm Sec5

/-! ### The totals of the angle words -/

/-- **The left total of an angle word**: the angle-change block telescopes. -/
theorem sum_angleWordL (κ : ℝ) (φ : ℕ → ℝ) (m : ℕ) {n : ℕ} (ρ₀ : Fin n → ℝ) :
    ∑ i, angleWordL κ φ m ρ₀ i = -(chiC κ / sleLambda κ * (φ 0 - φ m)) + ∑ i, ρ₀ i := by
  rw [angleWordL, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Finset.sum_neg_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun i => angleChangeWeight κ φ i) m, sum_angleChangeWeight]

/-- **The right total of an angle word**: the new seed and the angle-change block telescope. -/
theorem sum_angleWordR (κ : ℝ) (φ : ℕ → ℝ) (m : ℕ) {n : ℕ} (ρ₀ : Fin n → ℝ) :
    ∑ j, angleWordR κ φ m ρ₀ j = chiC κ / sleLambda κ * (φ 0 - φ (m + 1)) + ∑ j, ρ₀ j := by
  rw [angleWordR, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have h := sum_angleChangeWeight κ (fun j => φ (j + 1)) m
  rw [← Fin.sum_univ_eq_sum_range (fun i => angleChangeWeight κ (fun j => φ (j + 1)) i) m] at h
  have e : ∀ i : Fin m, angleChangeWeight κ φ ((i : ℕ) + 1) = angleChangeWeight κ (fun j => φ (j + 1)) i :=
    fun i => rfl
  simp only [e, h]
  simp only [angleChangeWeight]
  ring


/-! ### The far block of a presented slow shell -/

variable {κ : ℝ}

/-- **The totals of a presented word** are fixed by its two far heights: `(h_R − h_L)/λ − 2`, in both orientations
(`GW2Sdw.totals_eq_of_presentsO` for arbitrary weights). -/
theorem totals_of_presentsO (hκ : 0 < κ) {β : BoundaryWord} {sc : ℝ≥0} {flip : Bool} {nL nR : ℕ}
    {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} {hL hR : ℝ} (hfL : FarL β hL) (hfR : FarR β hR)
    (h : PresentsO κ β sc flip xL ρL xR ρR) :
    ∑ i, ρL i + ∑ j, ρR j = (hR - hL) / sleLambda κ - 2 := by
  have hb := BoundaryWord.isPiecewiseConstantBoundaryData β
  have sL := sum_flowLineRhoL_eq_of_far hκ hb 0 (farL_flowLine hκ hfL)
  have sR := sum_flowLineRhoR_eq_of_far hκ hb 0 (farR_flowLine hκ hfR)
  simp only [zero_mul, add_zero, Sec4.cumWeightLeft, Sec4.cumWeightRight] at sL sR
  cases flip with
  | false =>
    obtain ⟨eL, eR, -, -, hρL, hρR⟩ := h
    have e1 : ∑ i, ρL i = ∑ i, flowLineRhoL κ β.fn β.jumps 0 0 i := by
      rw [← hρL]
      exact (Equiv.sum_comp (finCongr eL) ρL).symm
    have e2 : ∑ j, ρR j = ∑ j, flowLineRhoR κ β.fn β.jumps 0 0 j := by
      rw [← hρR]
      exact (Equiv.sum_comp (finCongr eR) ρR).symm
    rw [e1, e2, sL, sR]
    ring
  | true =>
    obtain ⟨eL, eR, -, -, hρL, hρR⟩ := h
    have e1 : ∑ j, ρR j = ∑ i, flowLineRhoL κ β.fn β.jumps 0 0 i := by
      rw [← hρL]
      exact (Equiv.sum_comp (finCongr eL) ρR).symm
    have e2 : ∑ i, ρL i = ∑ j, flowLineRhoR κ β.fn β.jumps 0 0 j := by
      rw [← hρR]
      exact (Equiv.sum_comp (finCongr eR) ρL).symm
    rw [e1, e2, sL, sR]
    ring

/-- **The far block of a presented slow shell**: if the shell's angle words present a word with far heights
`h_L`, `h_R`, the far weights sum to `(h_R − h_L)/λ − 2` minus the net angle weight `(χ/λ)(φ_{mL} − φ_{mR+1})`. -/
theorem sum_far_of_presentsO (hκ : 0 < κ) {β : BoundaryWord} {sc : ℝ≥0} {flip : Bool} {z : SlowShell}
    {hL hR : ℝ} (hfL : FarL β hL) (hfR : FarR β hR)
    (h : PresentsO κ β sc flip z.xL (angleWordL κ z.φ z.mL z.ρL₀) z.xR (angleWordR κ z.φ z.mR z.ρR₀)) :
    ∑ i, z.ρL₀ i + ∑ j, z.ρR₀ j =
      (hR - hL) / sleLambda κ - 2 - chiC κ / sleLambda κ * (z.φ z.mL - z.φ (z.mR + 1)) := by
  have ht := totals_of_presentsO hκ hfL hfR h
  rw [sum_angleWordL, sum_angleWordR] at ht
  linear_combination ht

/-- **A lower bound for the drift constant of a presented slow shell**: with separated angles, the shell's
`stageDriftBound` is at least `8M/3 + (4/3)(|(h_R − h_L)/λ − 2| − M)`. -/
theorem le_stageDriftBound_of_presentsO (hκ : 0 < κ) (hκ4 : κ < 4) {β : BoundaryWord} {sc : ℝ≥0}
    {flip : Bool} {z : SlowShell} {hL hR : ℝ} (hφ : ∀ i, z.φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hfL : FarL β hL) (hfR : FarR β hR)
    (h : PresentsO κ β sc flip z.xL (angleWordL κ z.φ z.mL z.ρL₀) z.xR (angleWordR κ z.φ z.mR z.ρR₀)) :
    8 * angleWeightBound κ / 3 + 4 / 3 * (|(hR - hL) / sleLambda κ - 2| - angleWeightBound κ) ≤
      Prop59Stage.stageDriftBound κ z.ρL₀ z.ρR₀ := by
  have hs := sum_far_of_presentsO hκ hfL hfR h
  have hpos : 0 < chiC κ / sleLambda κ := div_pos (Sec4.chiC_pos hκ hκ4) (Sec4.sleLambda_pos hκ)
  have hM : angleWeightBound κ = chiC κ / sleLambda κ * Real.pi := by
    unfold angleWeightBound
    ring
  have hang : |chiC κ / sleLambda κ * (z.φ z.mL - z.φ (z.mR + 1))| ≤ angleWeightBound κ := by
    rw [abs_mul, abs_of_pos hpos, hM]
    refine mul_le_mul_of_nonneg_left ?_ hpos.le
    have h1 := hφ z.mL
    have h2 := hφ (z.mR + 1)
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have habs : |∑ i, z.ρL₀ i + ∑ j, z.ρR₀ j| ≤ ∑ i, |z.ρL₀ i| + ∑ j, |z.ρR₀ j| :=
    (abs_add_le _ _).trans (add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _))
  have he : (hR - hL) / sleLambda κ - 2 =
      (∑ i, z.ρL₀ i + ∑ j, z.ρR₀ j) + chiC κ / sleLambda κ * (z.φ z.mL - z.φ (z.mR + 1)) := by
    linear_combination -hs
  have hT : |(hR - hL) / sleLambda κ - 2| ≤ ∑ i, |z.ρL₀ i| + ∑ j, |z.ρR₀ j| + angleWeightBound κ := by
    rw [he]
    exact (abs_add_le _ _).trans (add_le_add habs hang)
  unfold Prop59Stage.stageDriftBound
  linarith

/-! ### The stage words of GEOM2's map -/

/-- The far-height difference of the stage words, in totals: `(2λ′ − 2πχ)/λ − 2 = 3κ/2 − 6`. -/
theorem stageWord_farTotal (hκ : 0 < κ) (a : ℝ) :
    ((sleLambda (16 / κ) - Real.pi * chiC κ + a) - (-sleLambda (16 / κ) + Real.pi * chiC κ + a)) /
      sleLambda κ - 2 = 3 * κ / 2 - 6 := by
  obtain ⟨h1, h2⟩ := totals_far_half_pi hκ
  simp only [Sec4.cumWeightLeft, Sec4.cumWeightRight] at h1 h2
  linear_combination h1 + h2

/-- **Every slow shell presenting a stage word of GEOM2's map has drift constant at least `8M/3 + (4/3)(4 − κ)`**,
whenever the decoded root record has a counterflow hull of positive extent on both sides (the far heights). -/
theorem le_stageDriftBound_schedWordMapX (hκ : 0 < κ) (hκ4 : κ < 4) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (θa : ℝ) (y : RecData)
    (hpos : 0 < markPos (rdrv (decHist N y).1) (rtime (decHist N y).1) 0)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) {sc : ℝ≥0} {flip : Bool}
    {z : SlowShell} (hφ : ∀ i, z.φ i ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    (h : PresentsO κ (schedWordMapX κ c' x s L N hN θa y) sc flip z.xL (angleWordL κ z.φ z.mL z.ρL₀) z.xR
      (angleWordR κ z.φ z.mR z.ρR₀)) :
    8 * angleWeightBound κ / 3 + 4 / 3 * (4 - κ) ≤ Prop59Stage.stageDriftBound κ z.ρL₀ z.ρR₀ := by
  have hfL := farL_upW (θa * chiC κ) (farL_baseWordX hκ c' x s L N hN y hpos)
  have hfR := farR_upW (θa * chiC κ) (farR_baseWordX hκ c' x s L N hN y hneg)
  have h' : PresentsO κ (GW2Rd.upW (θa * chiC κ) (baseWordX κ c' x s L N hN y)) sc flip z.xL
      (angleWordL κ z.φ z.mL z.ρL₀) z.xR (angleWordR κ z.φ z.mR z.ρR₀) := h
  have hb := le_stageDriftBound_of_presentsO hκ hκ4 hφ hfL hfR h'
  have hT := stageWord_farTotal hκ (θa * chiC κ)
  rw [hT, abs_of_neg (by linarith)] at hb
  have hM := angleWeightBound_eq hκ
  linarith

/-! ### The source's drift constant for constant data -/

theorem leftLim_const (c y : ℝ) : PiecewiseConstantBoundaryData.leftLim (fun _ => c) y = c :=
  tendsto_const_nhds.limUnder_eq

theorem rightLim_const (c y : ℝ) : PiecewiseConstantBoundaryData.rightLim (fun _ => c) y = c :=
  tendsto_const_nhds.limUnder_eq

theorem jumpSet_const (c : ℝ) (J : Finset ℝ) : PiecewiseConstantBoundaryData.jumpSet (fun _ => c) J = ∅ := by
  unfold PiecewiseConstantBoundaryData.jumpSet
  rw [Finset.filter_eq_empty_iff]
  intro y _
  rw [leftLim_const, rightLim_const]
  exact not_not.2 rfl

/-- Without jumps, the left flow-line word is its seed. -/
theorem sum_abs_flowLineRhoL_of_jumpSet {b : ℝ → ℝ} {J : Finset ℝ}
    (hJ : PiecewiseConstantBoundaryData.jumpSet b J = ∅) (κ x θ : ℝ) :
    ∑ i, |flowLineRhoL κ b J x θ i| =
      |-(PiecewiseConstantBoundaryData.leftLim b x + θ * chiC κ) / sleLambda κ - 1| := by
  have hc : ((PiecewiseConstantBoundaryData.jumpSet b J).filter (· < x)).card = 0 := by simp [hJ]
  have h0 : (0 : ℕ) < flowLineNL b J x := by unfold flowLineNL; omega
  rw [Fintype.sum_eq_single ⟨0, h0⟩]
  · rfl
  · intro i hi
    exfalso
    apply hi
    ext
    have := i.isLt
    simp only [flowLineNL, hc] at this ⊢
    omega

/-- Without jumps, the right flow-line word is its seed. -/
theorem sum_abs_flowLineRhoR_of_jumpSet {b : ℝ → ℝ} {J : Finset ℝ}
    (hJ : PiecewiseConstantBoundaryData.jumpSet b J = ∅) (κ x θ : ℝ) :
    ∑ j, |flowLineRhoR κ b J x θ j| =
      |(PiecewiseConstantBoundaryData.rightLim b x + θ * chiC κ) / sleLambda κ - 1| := by
  have hc : ((PiecewiseConstantBoundaryData.jumpSet b J).filter (x < ·)).card = 0 := by simp [hJ]
  have h0 : (0 : ℕ) < flowLineNR b J x := by unfold flowLineNR; omega
  rw [Fintype.sum_eq_single ⟨0, h0⟩]
  · rfl
  · intro i hi
    exfalso
    apply hi
    ext
    have := i.isLt
    simp only [flowLineNR, hc] at this ⊢
    omega

/-- **J32's drift constant for the zero boundary datum** is `8M/3 + 8/3`. -/
theorem sourceDriftBound_of_zero {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hb : c.b = fun _ => 0) :
    RootJ31.sourceDriftBound c r = 8 * angleWeightBound c.κ / 3 + 8 / 3 := by
  have hJ : PiecewiseConstantBoundaryData.jumpSet c.b c.jumps = ∅ := by
    rw [hb]
    exact jumpSet_const 0 _
  unfold RootJ31.sourceDriftBound Prop59Stage.stageDriftBound
  rw [sum_abs_flowLineRhoL_of_jumpSet hJ, sum_abs_flowLineRhoR_of_jumpSet hJ, hb, leftLim_const, rightLim_const]
  have hl : 0 < sleLambda c.κ := Sec4.sleLambda_pos c.hκ
  simp only [zero_mul, add_zero, zero_div, zero_sub, neg_zero]
  norm_num

/-! ### The drift clause against `sourceDriftBound` fails for every presenting shell -/

/-- **The slow shell's drift clause against `RootJ31.sourceDriftBound` is incompatible with the slow word**
(review N6, DECISIONS-FABLE-2 §F1): for `κ < 2` and the zero boundary datum, no slow shell with separated angles that
presents a stage word of GEOM2's map (the slow word of `FrameNSlowWordN`) satisfies
`ShellFactLe κ (sourceDriftBound c r)`. -/
theorem not_shellFactLe_sourceDriftBound {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hκ2 : c.κ < 2) (hb : c.b = fun _ => 0) (c' : BoundaryWord) (x : ℝ) (s : ℝ≥0)
    (L : List (ℝ × ℝ≥0)) (N : ℕ) (hN : L.length = N) (θa : ℝ) (y : RecData)
    (hpos : 0 < markPos (rdrv (decHist N y).1) (rtime (decHist N y).1) 0)
    (hneg : markPosL (rdrv (decHist N y).1) (rtime (decHist N y).1) 0 < 0) {sc : ℝ≥0} {flip : Bool}
    {z : SlowShell} (hz : ShellFactLe c.κ (RootJ31.sourceDriftBound c r) z)
    (h : PresentsO c.κ (schedWordMapX c.κ c' x s L N hN θa y) sc flip z.xL (angleWordL c.κ z.φ z.mL z.ρL₀) z.xR
      (angleWordR c.κ z.φ z.mR z.ρR₀)) : False := by
  have h1 := le_stageDriftBound_schedWordMapX c.hκ c.hκ4 c' x s L N hN θa y hpos hneg hz.1 h
  have h2 := hz.2.2
  rw [sourceDriftBound_of_zero c r hb] at h2
  linarith

/-! ### Presented frame words are ordered -/

/-- The flow-line positions of a word from `0` are ordered. -/
theorem antitone_flowLineXL (b : ℝ → ℝ) (J : Finset ℝ) : Antitone (flowLineXL b J 0) :=
  StrictAnti.antitone fun _ _ h => GW0.flowLineXL_lt b J 0 h

theorem monotone_flowLineXR (b : ℝ → ℝ) (J : Finset ℝ) : Monotone (flowLineXR b J 0) :=
  StrictMono.monotone fun _ _ h => GW0.flowLineXR_lt b J 0 h

/-- **A presenting frame word is an ordered force word**: the frame positions of any presentation `PresentsO` of a
word are its flow-line positions, rescaled (and reflected with the sides exchanged when `flip`). -/
theorem isOrderedForceWord_of_presentsO {κ : ℝ} {β : BoundaryWord} {sc : ℝ≥0} (hsc : sc ≠ 0) {flip : Bool}
    {nL nR : ℕ} {xL ρL : Fin nL → ℝ} {xR ρR : Fin nR → ℝ} (h : PresentsO κ β sc flip xL ρL xR ρR) :
    IsOrderedForceWord xL xR := by
  have hs : 0 < Real.sqrt sc := Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hsc))
  have hA := antitone_flowLineXL β.fn β.jumps
  have hM := monotone_flowLineXR β.fn β.jumps
  cases flip with
  | false =>
    obtain ⟨eL, eR, hxL, hxR, -, -⟩ := h
    have fL : ∀ i, Real.sqrt sc * xL i = flowLineXL β.fn β.jumps 0 (Fin.cast eL.symm i) := fun i => by
      simpa using congrFun hxL (Fin.cast eL.symm i)
    have fR : ∀ j, Real.sqrt sc * xR j = flowLineXR β.fn β.jumps 0 (Fin.cast eR.symm j) := fun j => by
      simpa using congrFun hxR (Fin.cast eR.symm j)
    refine ⟨fun i i' hii' => ?_, fun i => ?_, fun j j' hjj' => ?_, fun j => ?_⟩
    · have := hA (Fin.cast_le_cast eL.symm |>.2 hii')
      rw [← fL, ← fL] at this
      exact le_of_mul_le_mul_left this hs
    · have := GW3Word.flowLineXL_nonpos β.fn β.jumps (Fin.cast eL.symm i)
      rw [← fL] at this
      nlinarith
    · have := hM (Fin.cast_le_cast eR.symm |>.2 hjj')
      rw [← fR, ← fR] at this
      exact le_of_mul_le_mul_left this hs
    · have := GW3Word.flowLineXR_nonneg β.fn β.jumps (Fin.cast eR.symm j)
      rw [← fR] at this
      nlinarith
  | true =>
    obtain ⟨eL, eR, hxL, hxR, -, -⟩ := h
    have fR : ∀ j, -(Real.sqrt sc * xR j) = flowLineXL β.fn β.jumps 0 (Fin.cast eL.symm j) := fun j => by
      simpa using congrFun hxL (Fin.cast eL.symm j)
    have fL : ∀ i, -(Real.sqrt sc * xL i) = flowLineXR β.fn β.jumps 0 (Fin.cast eR.symm i) := fun i => by
      simpa using congrFun hxR (Fin.cast eR.symm i)
    refine ⟨fun i i' hii' => ?_, fun i => ?_, fun j j' hjj' => ?_, fun j => ?_⟩
    · have := hM (Fin.cast_le_cast eR.symm |>.2 hii')
      rw [← fL, ← fL] at this
      exact le_of_mul_le_mul_left (by linarith) hs
    · have := GW3Word.flowLineXR_nonneg β.fn β.jumps (Fin.cast eR.symm i)
      rw [← fL] at this
      nlinarith
    · have := hA (Fin.cast_le_cast eL.symm |>.2 hjj')
      rw [← fR, ← fR] at this
      exact le_of_mul_le_mul_left (by linarith) hs
    · have := GW3Word.flowLineXL_nonpos β.fn β.jumps (Fin.cast eL.symm j)
      rw [← fR] at this
      nlinarith

end InteractingSLE.Theorem14.GW2Rw
