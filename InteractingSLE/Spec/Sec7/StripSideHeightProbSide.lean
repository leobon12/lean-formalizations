/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.StripSideHeightProbMean
import InteractingSLE.Spec.Sec7.SideHeightGeom
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Spec.Zhan.ConstDriftTraceRs
import InteractingSLE.Spec.Sec7.SideHeightHull

/-!
# (S), probabilistic half, step 3: the side values of the stop word's mean

Packet PROVE-STRIPSYS16. Specification §7.4, proof of Aux. lemma 130 (`source/spec/p385-432.md` L440–L456, p. 411):
"In each own chart the right-side height is `λ − θχ`, with its inherited derivative-logarithm lift." Given the
records, the continuation's conditional mean read in its own record chart is the bounded harmonic mean of the stop word
`stopWord κ (β, θ, record)` (`ae_condExp_cexp_stopChart`); this file reads off its side values. The mark positions of
the stop word are read from the record driver (`Exist.StagedLaw.markPos`, an infimum over the alive rational points);
no force-point process is needed.

* `rightImg_sub_le_markPos`: the geometric image of `0⁺` (an infimum over all alive real points) lies left of the
  record position (an infimum over the alive rational points);
* `markPos_nonneg`, `markPos_mono`, `ne_top_iInf_markTerm`: the record positions of right marks are finite,
  nonnegative and increasing in the mark;
* **`lt_markPos_of_tendsto_fwdMap`**: a real limit `y` of `f_q` along an approach to a point of `ℍ` from `ℍ ∖ K_q` lies
  strictly between the record positions of `0⁻` and `0⁺` (the landed slit bounds
  `SideHeight.lt_rightImg_sub_of_extendFrom_mem_H'` for the frozen driver).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace StripSideHeightProb

open Exist.StagedLaw MartChar.RealFlow

/-! ### The record positions of the right marks -/

section MarkPos

variable {w : ℝ → ℝ} {T : ℝ}

/-- A real point above the driver on `[0, T]` is alive and has a forward solution. -/
theorem exists_alive_rat (hw : Continuous w) (hT : 0 ≤ T) (x : ℝ) :
    ∃ q : ℚ, x < q ∧ ∃ u, QuantumZipper.IsForwardSol w ((q : ℝ) : ℂ) T u := by
  obtain ⟨s₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hT) hw.continuousOn
  obtain ⟨q, hq⟩ := exists_rat_gt (max x (w s₀))
  refine ⟨q, (le_max_left _ _).trans_lt hq, ?_⟩
  have halive : Alive w q T := alive_of_forall_lt hw hT fun s hs => by
    have := hmax hs
    simp only [mem_ofPred_eq] at this
    linarith [le_max_right x (w s₀)]
  exact ⟨_, WangWu.isForwardSol_of_alive hw halive⟩

/-- The infimum defining a record position is not `⊤`. -/
theorem ne_top_iInf_markTerm (hw : Continuous w) (hT : 0 ≤ T) (x : ℝ) : (⨅ q : ℚ, markTerm w T x q) ≠ ⊤ := by
  classical
  obtain ⟨q, hxq, hsol⟩ := exists_alive_rat hw hT x
  refine ne_top_of_le_ne_top ?_ (iInf_le _ q)
  simp only [markTerm, hxq, hsol, and_self, ↓reduceIte]
  exact EReal.coe_ne_top _

/-- The terms of a right record position from `x ≥ 0` are nonnegative. -/
theorem zero_le_markTerm (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : 0 ≤ x) (q : ℚ) :
    (0 : EReal) ≤ markTerm w T x q := by
  classical
  unfold markTerm
  split_ifs with hq
  · obtain ⟨hxq, u, hu⟩ := hq
    have halive : Alive w q T := Lemma76E.alive_of_isForwardSol hw hT (by rw [hw0]; linarith) hu
    have hu' := WangWu.isForwardSol_of_alive hw halive
    have hf := fwdMap_eq_of_isForwardSol hw hu' ⟨hT, le_rfl⟩
    rw [hf]
    have hpos := halive.lt_gImg hw ⟨hT, le_rfl⟩
    simp only [gImg] at hpos
    exact EReal.coe_nonneg.2 (by simp; linarith)
  · exact le_top

theorem zero_le_iInf_markTerm (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : 0 ≤ x) :
    (0 : EReal) ≤ ⨅ q : ℚ, markTerm w T x q :=
  le_iInf (zero_le_markTerm hw hw0 hT hx)

theorem markPos_nonneg (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ markPos w T x :=
  EReal.toReal_nonneg (zero_le_iInf_markTerm hw hw0 hT hx)

/-- **The right record positions increase with the mark.** -/
theorem markPos_mono (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x x' : ℝ} (hx : 0 ≤ x) (hxx' : x ≤ x') :
    markPos w T x ≤ markPos w T x' := by
  classical
  have hle : (⨅ q : ℚ, markTerm w T x q) ≤ ⨅ q : ℚ, markTerm w T x' q := by
    refine iInf_mono fun q => ?_
    unfold markTerm
    by_cases h' : x' < q ∧ ∃ u, QuantumZipper.IsForwardSol w ((q : ℝ) : ℂ) T u
    · have h : x < q ∧ ∃ u, QuantumZipper.IsForwardSol w ((q : ℝ) : ℂ) T u := ⟨hxx'.trans_lt h'.1, h'.2⟩
      simp only [h, h', and_self, ↓reduceIte, le_refl]
    · simp only [h', ↓reduceIte, le_top]
  have hbot : (⨅ q : ℚ, markTerm w T x q) ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot 0) (zero_le_iInf_markTerm hw hw0 hT hx)
  exact EReal.toReal_le_toReal hle hbot (ne_top_iInf_markTerm hw hT x')

/-- **The geometric image of `0⁺` lies left of its record position**: `R_T − W_T ≤ markPos w T 0`. -/
theorem rightImg_sub_le_markPos (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) :
    rightImg w 0 T - w T ≤ markPos w T 0 := by
  classical
  have hlow : ∀ q : ℚ, ((rightImg w 0 T - w T : ℝ) : EReal) ≤ markTerm w T 0 q := by
    intro q
    unfold markTerm
    split_ifs with hq
    · obtain ⟨hq0, u, hu⟩ := hq
      have halive : Alive w q T := Lemma76E.alive_of_isForwardSol hw hT (by rw [hw0]; exact_mod_cast hq0) hu
      have h1 := rightImg_le_gImg hw hT (show (0 : ℝ) < q by exact_mod_cast hq0) halive
      have hu' := WangWu.isForwardSol_of_alive hw halive
      have hf := fwdMap_eq_of_isForwardSol hw hu' ⟨hT, le_rfl⟩
      rw [hf]
      simp only [gImg] at h1
      exact EReal.coe_le_coe_iff.2 (by simp; linarith)
    · exact le_top
  have hge : ((rightImg w 0 T - w T : ℝ) : EReal) ≤ ⨅ q : ℚ, markTerm w T 0 q := le_iInf hlow
  have hbot : (⨅ q : ℚ, markTerm w T 0 q) ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hge
  unfold markPos
  rw [← EReal.coe_le_coe_iff, EReal.coe_toReal (ne_top_iInf_markTerm hw hT 0) hbot]
  exact hge

end MarkPos

/-! ### The left marks and the congruence in the driver -/

section Left

variable {w : ℝ → ℝ} {T : ℝ}

theorem markPosL_nonpos (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x : ℝ} (hx : x ≤ 0) :
    markPosL w T x ≤ 0 := by
  have := markPos_nonneg (w := fun s => -w s) hw.neg (by simp [hw0]) hT (neg_nonneg.2 hx)
  unfold markPosL
  linarith

/-- **The left record positions decrease with the mark** (further left marks sit further left). -/
theorem markPosL_anti (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) {x x' : ℝ} (hx : x ≤ 0)
    (hx'x : x' ≤ x) : markPosL w T x' ≤ markPosL w T x := by
  have := markPos_mono (w := fun s => -w s) hw.neg (by simp [hw0]) hT (neg_nonneg.2 hx) (neg_le_neg hx'x)
  unfold markPosL
  linarith

/-- The record position of `0⁻` lies left of the geometric image of `0⁻`. -/
theorem markPosL_le_neg_rightImg (hw : Continuous w) (hw0 : w 0 = 0) (hT : 0 ≤ T) :
    markPosL w T 0 ≤ -rightImg (fun s => -w s) 0 T - w T := by
  have := rightImg_sub_le_markPos (w := fun s => -w s) hw.neg (by simp [hw0]) hT
  unfold markPosL
  rw [neg_zero]
  linarith

/-- The record positions only read the driver up to the record time. -/
theorem markPos_congr {w' : ℝ → ℝ} (h : EqOn w w' (Icc 0 T)) (x : ℝ) : markPos w T x = markPos w' T x := by
  unfold markPos markTerm
  congr 1
  refine iInf_congr fun q => ?_
  have h1 : (∃ u, QuantumZipper.IsForwardSol w ((q : ℝ) : ℂ) T u) ↔
      ∃ u, QuantumZipper.IsForwardSol w' ((q : ℝ) : ℂ) T u :=
    exists_congr fun u => Ito.isForwardSol_iff_of_eqOn h u
  by_cases hq : x < q ∧ ∃ u, QuantumZipper.IsForwardSol w ((q : ℝ) : ℂ) T u
  · have hq' : x < q ∧ ∃ u, QuantumZipper.IsForwardSol w' ((q : ℝ) : ℂ) T u := ⟨hq.1, h1.1 hq.2⟩
    simp only [hq, hq', and_self, ↓reduceIte, Ito.fwdMap_congr_of_eqOn h]
  · have hq' : ¬ (x < q ∧ ∃ u, QuantumZipper.IsForwardSol w' ((q : ℝ) : ℂ) T u) := fun h' =>
      hq ⟨h'.1, h1.2 h'.2⟩
    simp only [hq, hq', ↓reduceIte]

theorem markPosL_congr {w' : ℝ → ℝ} (h : EqOn w w' (Icc 0 T)) (x : ℝ) : markPosL w T x = markPosL w' T x := by
  unfold markPosL
  rw [markPos_congr (w := fun s => -w s) (w' := fun s => -w' s) (fun s hs => by simp only [h hs])]

end Left

/-! ### The approach limits lie strictly between the record positions of `0⁻` and `0⁺` -/

/-- **A real limit of `f_q` along an approach to a point of `ℍ` lies strictly between the record positions of `0⁻`
and `0⁺`** (the slit bounds `SideHeight.lt_rightImg_sub_of_extendFrom_mem_H'`,
`SideHeight.neg_rightImg_sub_lt_of_extendFrom_mem_H'` for the frozen driver, and `rightImg_sub_le_markPos`). -/
theorem markPosL_lt_lt_markPos_of_tendsto_fwdMap {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ζ γ) (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < ζ) {p : ℂ} (hpH : p ∈ H) {F : Filter ℂ} [F.NeBot]
    (hF : F ≤ 𝓝[H \ fwdHull (fun s : ℝ => w s.toNNReal) q] p) {y : ℝ}
    (hy : Tendsto (fwdMap (fun s : ℝ => w s.toNNReal) q) F (𝓝 (y : ℂ))) :
    markPosL (fun s : ℝ => w s.toNNReal) q 0 < y ∧ y < markPos (fun s : ℝ => w s.toNNReal) q 0 := by
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  have ht₂0 : 0 ≤ t₂ := (NNReal.coe_nonneg q).trans hqt₂.le
  have hW : Continuous (frozenDrive w t₂) := continuous_frozenDrive_of_lt hwc ht₂
  have hW0 : frozenDrive w t₂ 0 = 0 := by rw [frozenDrive_zero ht₂0, hw0]
  have hB := (hγ.isLoewnerTraceLT ht₂).hasBdryLimits hW hW0 q.coe_nonneg hqt₂
  have hFy : extendFrom H (fwdMapInv (frozenDrive w t₂) q) y ∈ H := by
    rw [SideHeight.extendFrom_eq_of_tendsto_fwdMap hγ hwc hw0 hqt₂ ht₂ hF hy]
    exact hpH
  have hR := SideHeight.lt_rightImg_sub_of_extendFrom_mem_H' hB hW hW0 q.coe_nonneg hFy
  have hL := SideHeight.neg_rightImg_sub_lt_of_extendFrom_mem_H' hB hW hW0 q.coe_nonneg hFy
  have heq : EqOn (frozenDrive w t₂) (fun s : ℝ => w s.toNNReal) (Icc 0 (q : ℝ)) := fun r hr =>
    frozenDrive_eq ⟨hr.1, hr.2.trans hqt₂.le⟩
  have hmR := rightImg_sub_le_markPos hW hW0 q.coe_nonneg
  have hmL := markPosL_le_neg_rightImg hW hW0 q.coe_nonneg
  rw [markPos_congr heq] at hmR
  rw [markPosL_congr heq] at hmL
  exact ⟨by linarith, by linarith⟩

/-! ### The side values of the stop word's mean -/

section Side

open Restart Exist.Staged

variable {κ : ℝ}

/-- **The record positions of the stop word are in mark order** (left marks nonpositive and decreasing, right marks
nonnegative and increasing), since the flow-line word is ordered (`Theorem15.isOrderedForceWord_flowLine`). -/
theorem isMarkOrder_stopWord (c : BoundaryWord) (r : RecData) :
    IsMarkOrder (flowLineNL c.fn c.jumps 0) (flowLineNR c.fn c.jumps 0)
      (fun i => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) := by
  obtain ⟨hLa, hL0, hRm, hR0⟩ := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  have hxL : ∀ i (hi : i < flowLineNL c.fn c.jumps 0),
      (padFL 0 0 c.fn c.jumps).1.1 i = flowLineXL c.fn c.jumps 0 ⟨i, hi⟩ := fun i hi => by
    simp only [padFL, hi, ↓reduceDIte]
  have hxR : ∀ j (hj : j < flowLineNR c.fn c.jumps 0),
      (padFL 0 0 c.fn c.jumps).1.2 j = flowLineXR c.fn c.jumps 0 ⟨j, hj⟩ := fun j hj => by
    simp only [padFL, hj, ↓reduceDIte]
  refine ⟨fun i j hij hj => ?_, fun i hi => ?_, fun i j hij hj => ?_, fun i hi => ?_⟩
  · have hi : i < flowLineNL c.fn c.jumps 0 := lt_of_le_of_lt hij hj
    show markPosL _ _ _ ≤ markPosL _ _ _
    rw [hxL i hi, hxL j hj]
    exact markPosL_anti hw hw0 hT (hL0 _) (hLa (Fin.mk_le_mk.2 hij))
  · show markPosL _ _ _ ≤ 0
    rw [hxL i hi]
    exact markPosL_nonpos hw hw0 hT (hL0 _)
  · have hi : i < flowLineNR c.fn c.jumps 0 := lt_of_le_of_lt hij hj
    show markPos _ _ _ ≤ markPos _ _ _
    rw [hxR i hi, hxR j hj]
    exact markPos_mono hw hw0 hT (hR0 _) (hRm (Fin.mk_le_mk.2 hij))
  · show 0 ≤ markPos _ _ _
    rw [hxR i hi]
    exact markPos_nonneg hw hw0 hT (hR0 _)

/-- The mean of the stop word is the bounded harmonic extension of the force data at the record positions, minus
`θχ`. -/
theorem exists_eqOn_mean_stopWord (c : BoundaryWord) (θ : ℝ) (r : RecData) :
    ∃ u : ℂ → ℝ, IsBoundedHarmonicExtension
      (forceBoundaryData κ (fun i : Fin (flowLineNL c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.1 i)
        (fun j : Fin (flowLineNR c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.2 j)
        (fun i : Fin (flowLineNL c.fn c.jumps 0) => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
        (fun j : Fin (flowLineNR c.fn c.jumps 0) => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)))
      (forceJumpSet
        (fun i : Fin (flowLineNL c.fn c.jumps 0) => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
        (fun j : Fin (flowLineNR c.fn c.jumps 0) => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)))
      u ∧ ∀ z ∈ H, (stopWord κ (c, θ, r)).mean z = u z - θ * chiC κ := by
  obtain ⟨u, hu⟩ := Sec4.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (fun i : Fin (flowLineNL c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.1 i)
    (fun j : Fin (flowLineNR c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.2 j)
    (fun i : Fin (flowLineNL c.fn c.jumps 0) => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
    (fun j : Fin (flowLineNR c.fn c.jumps 0) => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j))
  have heq := eqOn_mean_forceWord κ (padFL κ θ c.fn c.jumps).2.1 (padFL κ θ c.fn c.jumps).2.2 (θ * chiC κ)
    (isMarkOrder_stopWord c r) hu
  refine ⟨u, hu, fun z hz => ?_⟩
  have h := heq hz
  change u z = (stopWord κ (c, θ, r)).mean z + θ * chiC κ at h
  linarith

/-- **Right side value `λ − θχ` of the stop word's mean**: at every real `y` strictly between `0` and the record
position of `0⁺`. -/
theorem tendsto_mean_stopWord_of_pos (c : BoundaryWord) (θ : ℝ) (r : RecData) {y : ℝ} (hy0 : 0 < y)
    (hyR : y < markPos (rdrv r) (rtime r) 0) :
    Tendsto (stopWord κ (c, θ, r)).mean (𝓝[H] (y : ℂ)) (𝓝 (sleLambda κ - θ * chiC κ)) := by
  obtain ⟨hLa, hL0, hRm, hR0⟩ := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  obtain ⟨u, hu, hmean⟩ := exists_eqOn_mean_stopWord (κ := κ) c θ r
  have hRgt : ∀ j : Fin (flowLineNR c.fn c.jumps 0),
      y < markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) := fun j => by
    have hx : (padFL 0 0 c.fn c.jumps).1.2 j = flowLineXR c.fn c.jumps 0 j := by
      simp only [padFL, j.2, ↓reduceDIte]
    rw [hx]
    exact hyR.trans_le (markPos_mono hw hw0 hT le_rfl (hR0 j))
  have hLlt : ∀ i : Fin (flowLineNL c.fn c.jumps 0),
      markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) < y := fun i => by
    have hx : (padFL 0 0 c.fn c.jumps).1.1 i = flowLineXL c.fn c.jumps 0 i := by
      simp only [padFL, i.2, ↓reduceDIte]
    rw [hx]
    exact (markPosL_nonpos hw hw0 hT (hL0 i)).trans_lt hy0
  have hyS : y ∉ forceJumpSet
      (fun i : Fin (flowLineNL c.fn c.jumps 0) => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) := by
    intro hmem
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hmem
    rcases hmem with h0 | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hy0.ne' h0
    · exact (hLlt i).ne hi
    · exact (hRgt i).ne' hi
  have hbd := hu.2.2 y hyS
  have hdata : forceBoundaryData κ
      (fun i : Fin (flowLineNL c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.1 i)
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.2 j)
      (fun i : Fin (flowLineNL c.fn c.jumps 0) => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) y =
      sleLambda κ := by
    simp only [forceBoundaryData, show ¬ y < 0 from not_lt.2 hy0.le, ↓reduceIte]
    rw [Finset.filter_false_of_mem fun i _ => not_le.2 (hRgt i), Finset.sum_empty, add_zero, mul_one, sleLambda]
  rw [hdata] at hbd
  refine (hbd.sub_const (θ * chiC κ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz using (hmean z hz).symm

/-- **Left side value `−λ − θχ` of the stop word's mean**: at every real `y` strictly between the record position of
`0⁻` and `0`. -/
theorem tendsto_mean_stopWord_of_neg (c : BoundaryWord) (θ : ℝ) (r : RecData) {y : ℝ} (hy0 : y < 0)
    (hyL : markPosL (rdrv r) (rtime r) 0 < y) :
    Tendsto (stopWord κ (c, θ, r)).mean (𝓝[H] (y : ℂ)) (𝓝 (-sleLambda κ - θ * chiC κ)) := by
  obtain ⟨hLa, hL0, hRm, hR0⟩ := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hw := continuous_rdrv r
  have hw0 := rdrv_zero r
  have hT := rtime_nonneg r
  obtain ⟨u, hu, hmean⟩ := exists_eqOn_mean_stopWord (κ := κ) c θ r
  have hRgt : ∀ j : Fin (flowLineNR c.fn c.jumps 0),
      y < markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j) := fun j => by
    have hx : (padFL 0 0 c.fn c.jumps).1.2 j = flowLineXR c.fn c.jumps 0 j := by
      simp only [padFL, j.2, ↓reduceDIte]
    rw [hx]
    exact hy0.trans_le (markPos_nonneg hw hw0 hT (hR0 j))
  have hLlt : ∀ i : Fin (flowLineNL c.fn c.jumps 0),
      markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i) < y := fun i => by
    have hx : (padFL 0 0 c.fn c.jumps).1.1 i = flowLineXL c.fn c.jumps 0 i := by
      simp only [padFL, i.2, ↓reduceDIte]
    rw [hx]
    exact (markPosL_anti hw hw0 hT le_rfl (hL0 i)).trans_lt hyL
  have hyS : y ∉ forceJumpSet
      (fun i : Fin (flowLineNL c.fn c.jumps 0) => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) := by
    intro hmem
    simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range] at hmem
    rcases hmem with h0 | ⟨i, hi⟩ | ⟨i, hi⟩
    · exact hy0.ne h0
    · exact (hLlt i).ne hi
    · exact (hRgt i).ne' hi
  have hbd := hu.2.2 y hyS
  have hdata : forceBoundaryData κ
      (fun i : Fin (flowLineNL c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.1 i)
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => (padFL κ θ c.fn c.jumps).2.2 j)
      (fun i : Fin (flowLineNL c.fn c.jumps 0) => markPosL (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.1 i))
      (fun j : Fin (flowLineNR c.fn c.jumps 0) => markPos (rdrv r) (rtime r) ((padFL 0 0 c.fn c.jumps).1.2 j)) y =
      -sleLambda κ := by
    simp only [forceBoundaryData, hy0, ↓reduceIte]
    rw [Finset.filter_false_of_mem fun i _ => not_lt.2 (hLlt i).le, Finset.sum_empty, add_zero, mul_one, sleLambda]
  rw [hdata] at hbd
  refine (hbd.sub_const (θ * chiC κ)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz using (hmean z hz).symm

end Side

/-! ### The conditional side heights of the continuation, in its own chart -/

section Heights

open Restart

variable {κ : ℝ}

/-- The forward map of a driver continuous before its lifetime maps the complement of the hull into `ℍ`. -/
theorem mapsTo_fwdMap_rpath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {q : ℝ≥0}
    (hq : (q : ℝ≥0∞) < ζ) :
    MapsTo (fwdMap (fun s : ℝ => w s.toNNReal) q) (H \ fwdHull (fun s : ℝ => w s.toNNReal) q) H := by
  obtain ⟨t₂, hqt₂, ht₂⟩ := exists_real_btwn_of_lt hq
  have hW := continuous_frozenDrive_of_lt hwc ht₂
  have heq : ∀ r ∈ Icc (0 : ℝ) t₂, (fun s : ℝ => w s.toNNReal) r = frozenDrive w t₂ r := fun r hr =>
    (frozenDrive_eq hr).symm
  have hK := fwdHull_eq_of_eqOn q.coe_nonneg hqt₂ heq
  have hM : fwdMap (fun s : ℝ => w s.toNNReal) q = fwdMap (frozenDrive w t₂) q :=
    funext fun z => fwdMap_eq_of_eqOn q.coe_nonneg fun r hr => heq r ⟨hr.1, hr.2.trans hqt₂.le⟩
  rw [hK, hM]
  exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW q.coe_nonneg

/-- **The continuation's side heights in its own chart** (the conditional side heights of (S)): for the record `r` of
the continuation stopped at its own time `q = rtime r`, any driver `w'` continuous before its lifetime `ζ' > q` that
agrees with the record driver on `[0, q]` and has a generating trace `α'`, the stop word's mean read in the chart,
`v' = 𝔤 ∘ f_q − χ arg f_q′`, has the side heights `±λ − θχ` (`StripGeom.HasSideHeights`, with the lift of the chart) at
every point of `ℍ`. -/
theorem hasSideHeights_stopWord (c : BoundaryWord) (θ : ℝ) (r : RecData) {w' : ℝ≥0 → ℝ} {α' : ℝ≥0 → ℂ}
    {ζ' : ℝ≥0∞} {q : ℝ≥0} (hrt : rtime r = q) (hγ : IsGeneratingTrace w' ζ' α')
    (hwc : ContinuousOn w' {t | (t : ℝ≥0∞) < ζ'}) (hw0 : w' 0 = 0) (hagree : ∀ s : ℝ≥0, s ≤ q → w' s = recW r s)
    (hq : (q : ℝ≥0∞) < ζ') {p : ℂ} (hpH : p ∈ H) :
    StripGeom.HasSideHeights κ θ α' 0 w' q p
      (fun z => (stopWord κ (c, θ, r)).mean (fwdMap (fun s : ℝ => w' s.toNNReal) q z) -
        chiC κ * (logDerivFwd (fun s : ℝ => w' s.toNNReal) q z).im) (fun _ => 0) := by
  intro F hF hFle y hy
  have hfill := SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hγ hq
  have hF' : F ≤ 𝓝[H \ fwdHull (fun s : ℝ => w' s.toNNReal) q] p := by rw [hfill]; exact hFle
  have hy' : Tendsto (fwdMap (fun s : ℝ => w' s.toNNReal) q) F (𝓝 (y : ℂ)) := by
    simpa only [sub_zero, Complex.ofReal_zero] using hy
  obtain ⟨hL, hR⟩ := markPosL_lt_lt_markPos_of_tendsto_fwdMap hγ hwc hw0 hq hpH hF' hy'
  have heqr : EqOn (fun s : ℝ => w' s.toNNReal) (rdrv r) (Icc 0 (q : ℝ)) := fun x hx => by
    change w' x.toNNReal = recW r x.toNNReal
    exact hagree _ (Real.toNNReal_le_iff_le_coe.2 hx.2)
  rw [markPos_congr heqr] at hR
  rw [markPosL_congr heqr] at hL
  have hev : ∀ᶠ z in F, z ∈ H \ fwdHull (fun s : ℝ => w' s.toNNReal) q := hF' self_mem_nhdsWithin
  have hyH : Tendsto (fwdMap (fun s : ℝ => w' s.toNNReal) q) F (𝓝[H] (y : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hy', hev.mono fun z hz => mapsTo_fwdMap_rpath hwc hq hz⟩
  have hfun : (fun z => (fun z => (stopWord κ (c, θ, r)).mean (fwdMap (fun s : ℝ => w' s.toNNReal) q z) -
        chiC κ * (logDerivFwd (fun s : ℝ => w' s.toNNReal) q z).im) z + (fun _ => (0 : ℝ)) z +
        chiC κ * (logDerivFwd (fun s : ℝ => w' s.toNNReal) q (z - ((0 : ℝ) : ℂ))).im) =
      fun z => (stopWord κ (c, θ, r)).mean (fwdMap (fun s : ℝ => w' s.toNNReal) q z) := by
    funext z
    simp only [Complex.ofReal_zero, sub_zero]
    ring
  rw [hfun]
  refine ⟨fun hy0 => ?_, fun hy0 => ?_⟩
  · have hyR : y < markPos (rdrv r) (rtime r) 0 := by rw [hrt]; exact hR
    exact (tendsto_mean_stopWord_of_pos c θ r hy0 hyR).comp hyH
  · have hyL : markPosL (rdrv r) (rtime r) 0 < y := by rw [hrt]; exact hL
    exact (tendsto_mean_stopWord_of_neg c θ r hy0 hyL).comp hyH

end Heights

/-! ### (S) for the angle-varying path, from the stage mean -/

section Assembly

open Restart StripSideHeight

variable {κ : ℝ}

/-- **(S), deterministic assembly.** Let `α` be an injective generating trace of a driver `W'`, continuous before the
lifetime `ζ > t₀ + r`, which agrees on `[0, t₀ + r]` with the concatenation of `w₀` (up to `t₀`) and `w₁ = recW r₁`,
the record driver of the continuation stopped at `r = rtime r₁`. If `v + 𝔥₀` equals the stage mean `𝔤 ∘ F − χ ℓ` on
the domain of the two-stage chart (the identity of `ae_apply_eq_stageMean`; `𝔤` the stop word's mean, `F`, `ℓ` the
chart and its lift), then `α` has the side heights `±λ − θχ` (`StripGeom.HasSideHeights`) at every trace point `α(t₁)`,
`t₀ < t₁`, in `ℍ`, at the stop `t₀ + r` — the input `hside₁` of `StripGeom.false_of_sameArc_sideHeights(_half_pi)`. -/
theorem hasSideHeights_of_eqOn_stageMean {w₀ w₁ : ℝ≥0 → ℝ} (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) {t₀ r : ℝ≥0}
    (r₁ : RecData) (hw₁ : w₁ = recW r₁) (hrt : rtime r₁ = r) (c : BoundaryWord) (θ : ℝ) {W' : ℝ≥0 → ℝ}
    {α : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hg : IsGeneratingTrace W' ζ α) (hWc : ContinuousOn W' {s | (s : ℝ≥0∞) < ζ})
    (hW0 : W' 0 = 0) (hagree : ∀ s : ℝ≥0, s ≤ t₀ + r → W' s = catPath w₀ t₀ w₁ s)
    (hinj : InjOn α {t | (t : ℝ≥0∞) ≤ ζ}) (hTr : ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ) {t₁ : ℝ≥0} (hTt : t₀ < t₁)
    (ht₁ : (t₁ : ℝ≥0∞) < ζ) (hH : α t₁ ∈ H) {v u₀ : ℂ → ℝ}
    (hv : EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (c, θ, r₁)).mean ((twoChart w₀ t₀ w₁ r).1 z) -
      chiC κ * (twoChart w₀ t₀ w₁ r).2.2 z) (twoChart w₀ t₀ w₁ r).dom) :
    StripGeom.HasSideHeights κ θ α 0 W' (t₀ + r) (α t₁) v u₀ := by
  have h₁ : Continuous w₁ := by rw [hw₁]; exact LocalExt.continuous_histDrv _
  have h10 : w₁ 0 = 0 := by rw [hw₁]; exact LocalExt.histDrv_zero _
  have hα0 : (fun t => α t - ((0 : ℝ) : ℂ)) = α := funext fun t => by simp
  have hg0 : IsGeneratingTrace W' ζ (fun t => α t - ((0 : ℝ) : ℂ)) := by rw [hα0]; exact hg
  have hinj0 : InjOn (fun t => α t - ((0 : ℝ) : ℂ)) {t | (t : ℝ≥0∞) ≤ ζ} := by rw [hα0]; exact hinj
  -- the continuation's generating trace, alive past `r`
  obtain ⟨v₂, hv₂a, hv₂b⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTr
  have ht₀v : t₀ ≤ v₂ := le_trans le_self_add (show t₀ + r ≤ v₂ from by exact_mod_cast hv₂a.le)
  set u : ℝ≥0 := v₂ - t₀ with hu_def
  have htu : ((t₀ + u : ℝ≥0) : ℝ≥0∞) < ζ := by rw [hu_def, add_tsub_cancel_of_le ht₀v]; exact hv₂b
  have hru : (r : ℝ≥0∞) < u := by
    have : t₀ + r < v₂ := by exact_mod_cast hv₂a
    exact_mod_cast (lt_tsub_iff_left.2 this)
  have hg'' : IsGeneratingTrace (restartDrv W' t₀) u (Zhan.shiftTip W' t₀) :=
    Zhan.isGeneratingTrace_shiftTip hg hWc hW0 htu
  have hwc' : ContinuousOn (restartDrv W' t₀) {s | (s : ℝ≥0∞) < u} := by
    have hmap : MapsTo (fun s : ℝ≥0 => t₀ + s) {s | (s : ℝ≥0∞) < u} {s | (s : ℝ≥0∞) < ζ} := fun s hs => by
      have h1 : t₀ + s < t₀ + u := add_lt_add_right (by exact_mod_cast hs) t₀
      exact lt_trans (by exact_mod_cast h1) htu
    exact (hWc.comp (continuous_const.add continuous_id).continuousOn hmap).sub continuousOn_const
  have hw0' : restartDrv W' t₀ 0 = 0 := by simp [restartDrv]
  have hagree' : ∀ s : ℝ≥0, s ≤ r → restartDrv W' t₀ s = recW r₁ s := fun s hs => by
    have h1 := hagree (t₀ + s) (add_le_add_right hs t₀)
    have h2 := hagree t₀ le_self_add
    have h3 := congrFun (restartDrv_catPath (w₀ := w₀) (T₀ := t₀) h10) s
    simp only [restartDrv] at h3 ⊢
    rw [h1, h2, h3, hw₁]
  -- the side heights of the continuation at the chart image of `α(t₁)`
  have hp := sub_mem_H_diff_fwdHull_of_lt hg0 hWc hW0 hinj0 hTt ht₁ hH
  have ht₀ζ : (t₀ : ℝ≥0∞) < ζ := lt_trans (by exact_mod_cast hTt) ht₁
  have hpH := mapsTo_fwdMap_rpath hWc ht₀ζ hp
  have hside := hasSideHeights_stopWord (κ := κ) c θ r₁ hrt hg'' hwc' hw0' hagree' hru hpH
  -- the transport identity of the means
  have hr0 : EqOn (fun s : ℝ => W' s.toNNReal) (Ito.rpath w₀) (Icc 0 (t₀ : ℝ)) := fun x hx => by
    have hx' : x.toNNReal ≤ t₀ := Real.toNNReal_le_iff_le_coe.2 hx.2
    change W' x.toNNReal = w₀ x.toNNReal
    rw [hagree _ (hx'.trans le_self_add), catPath_of_le hx']
  have hr1 : EqOn (fun s : ℝ => restartDrv W' t₀ s.toNNReal) (Ito.rpath w₁) (Icc 0 (r : ℝ)) := fun x hx => by
    change restartDrv W' t₀ x.toNNReal = w₁ x.toNNReal
    rw [hagree' _ (Real.toNNReal_le_iff_le_coe.2 hx.2), hw₁]
  have hrc : EqOn (fun s : ℝ => W' s.toNNReal) (Ito.rpath (catPath w₀ t₀ w₁)) (Icc 0 ((t₀ + r : ℝ≥0) : ℝ)) :=
    fun x hx => hagree _ (Real.toNNReal_le_iff_le_coe.2 hx.2)
  have hmean : ∀ᶠ z in 𝓝[H \ fillH (α '' Icc 0 (t₀ + r))] α t₁,
      v z + u₀ z = (fun z => (stopWord κ (c, θ, r₁)).mean
          (fwdMap (fun s : ℝ => restartDrv W' t₀ s.toNNReal) r z) -
          chiC κ * (logDerivFwd (fun s : ℝ => restartDrv W' t₀ s.toNNReal) r z).im)
          (fwdMap (fun s : ℝ => W' s.toNNReal) t₀ (z - ((0 : ℝ) : ℂ))) +
        (fun _ => (0 : ℝ)) (fwdMap (fun s : ℝ => W' s.toNNReal) t₀ (z - ((0 : ℝ) : ℂ))) -
          chiC κ * (logDerivFwd (fun s : ℝ => W' s.toNNReal) t₀ (z - ((0 : ℝ) : ℂ))).im := by
    have hfill := SideHeight.fwdHull_eq_fillH_of_isGeneratingTrace hg hTr
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hzD : z ∈ (twoChart w₀ t₀ w₁ r).dom := by
      rw [← hfill] at hz
      obtain ⟨u', hu'⟩ := Ito.exists_isForwardSol_of_mem (NNReal.coe_nonneg _) hz
      rw [twoChart_dom_eq h₀ h00 h₁ h10, Chart.mem_dom_loewner_iff (continuous_rpath_catPath h₀ h₁ h10)
        (rpath_catPath_zero h00) (NNReal.coe_nonneg _)]
      exact ⟨hz.1, u', (Ito.isForwardSol_iff_of_eqOn hrc u').1 hu'⟩
    have hvz := hv hzD
    simp only at hvz
    rw [hvz]
    simp only [Complex.ofReal_zero, sub_zero, Ito.fwdMap_congr_of_eqOn hr0,
      Ito.logDerivFwd_congr_of_eqOn hr0 t₀.coe_nonneg le_rfl, Ito.fwdMap_congr_of_eqOn hr1,
      Ito.logDerivFwd_congr_of_eqOn hr1 r.coe_nonneg le_rfl]
    change (stopWord κ (c, θ, r₁)).mean (fwdMap (Ito.rpath w₁) r (fwdMap (Ito.rpath w₀) t₀ z)) -
        chiC κ * ((logDerivFwd (Ito.rpath w₁) r (fwdMap (Ito.rpath w₀) t₀ z)).im + 0 +
          ((logDerivFwd (Ito.rpath w₀) t₀ z).im + 0)) = _
    ring
  exact hasSideHeights_of_restart_of_lt (κ := κ) (θ := θ) (x := 0) hg0 hWc hW0 hinj0 hTr hTt ht₁ hH hg'' hru
    hmean hside

end Assembly

/-! ### (S): the side heights of the angle-varying path, almost surely -/

section Final

open Exist Exist.Staged Exist.StagedLaw Restart LocalSets

universe u

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ}
  {t₀ : ℝ≥0} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit mΩ [StandardBorelSpace Ω] in
theorem rtime_recsTwo_one {r : ℝ≥0} {ω : Ω} (hω : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E) :
    rtime (recsTwo κ b jumps θ₀ t₀ θ r E ω 1) = r := by
  change rtime (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1) = r
  rw [pastMap_two_one hω.1, rtime_recOf]
  simp only [stopTime, min_eq_left (lt_zeta_one_of_mem_goodEv hω).le, ENNReal.toNNReal_coe]

/-- **(S), the probabilistic half** (proof of Aux. lemma 130, p. 411: "In each own chart the right-side height is
`λ − θχ`, with its inherited derivative-logarithm lift"), for the two-angle path `η^{t₀,∞}_{θ₀,θ}` of a staged history
(`α = η^{1,∞}_{−π/2,θ₁}` of (RS13.1) for `t₀ = 1`, `θ₀ = −π/2`, `θ = θ₁`): almost surely on the good event, for every
harmonic representative `v` of the local-set mean `g` of a set `A` retained with the records (the marked local-set
structure `hmark`, e.g. the range of the path up to own time `t₀ + r`), every injective generating trace `α` of the
concatenated record driver alive past `t₀ + r`, and every trace point `α(t₁)` after the change, `t₀ < t₁`, in `ℍ`:
`α` has the side heights `±λ − θχ` at `α(t₁)` at the stop `t₀ + r` (`StripGeom.HasSideHeights`, the input `hside₁` of
`StripGeom.false_of_sameArc_sideHeights(_half_pi)`). -/
theorem ae_hasSideHeights_stage (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (r : ℝ≥0) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {A : Ω → Set ℂ} (hA : Measurable[mΩ, hittingSigma] A)
    (hloc : IsLocalSet A (WholeField.centredField h u₀) P)
    (hmark : WholeField.IsHistoryAvoidanceLocal (pastTwo κ b jumps θ₀ t₀ θ r E) A (WholeField.centredField h u₀) P)
    (hAD : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E →
      ((stopChart κ b jumps θ₀ t₀ θ r E ω).dom : Set ℂ) ⊆ H \ A ω ∧
        IsOpen ((H \ A ω) \ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom))
    {g : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A (WholeField.centredField h u₀) P g) :
    ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E → ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ z, v z * φ z) →
      ∀ (W' : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ) (ζ : ℝ≥0∞), IsGeneratingTrace W' ζ α →
        ContinuousOn W' {s | (s : ℝ≥0∞) < ζ} → W' 0 = 0 →
        (∀ s : ℝ≥0, s ≤ t₀ + r → W' s = catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀
          (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) s) →
        InjOn α {t | (t : ℝ≥0∞) ≤ ζ} → ((t₀ + r : ℝ≥0) : ℝ≥0∞) < ζ →
        ∀ t₁ : ℝ≥0, t₀ < t₁ → (t₁ : ℝ≥0∞) < ζ → α t₁ ∈ H →
          StripGeom.HasSideHeights κ θ α 0 W' (t₀ + r) (α t₁) v u₀ := by
  classical
  obtain ⟨β, -, hmean⟩ := ae_apply_eq_stageMean hκ hb hh hS hreg r hu₀ hA hloc hmark hAD hg
  -- the record drivers
  have hWc : ∀ (i : Fin 2) ω, Continuous (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω i)) := fun _ _ =>
    LocalExt.continuous_histDrv _
  have hW0 : ∀ (i : Fin 2) ω, recW (recsTwo κ b jumps θ₀ t₀ θ r E ω i) 0 = 0 := fun _ _ =>
    LocalExt.histDrv_zero _
  -- the domain, empty off the good event
  obtain ⟨D, hD⟩ : ∃ D : Ω → Set ℂ, D = fun ω => if ω ∈ goodEv κ b jumps θ₀ t₀ θ r E then
      ((stopChart κ b jumps θ₀ t₀ θ r E ω).dom : Set ℂ) else ∅ := ⟨_, rfl⟩
  -- the stage mean as a coupling mean of the concatenated record driver
  obtain ⟨m, hm⟩ : ∃ m : Ω → ℂ → ℝ, m = fun ω z => couplingMean κ
      (Ito.rpath (catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀ (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1))))
      ((t₀ + r : ℝ≥0) : ℝ) (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean z - u₀ z := ⟨_, rfl⟩
  -- on the domain the coupling mean is the two-stage chart expression
  have hcm : ∀ ω, ∀ z ∈ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom,
      couplingMean κ (Ito.rpath (catPath (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀
        (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)))) ((t₀ + r : ℝ≥0) : ℝ)
        (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean z =
      (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z) -
        chiC κ * (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z := by
    intro ω z hz
    have hz' : z ∈ (catChart (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0)) t₀
        (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) r).dom := by
      rw [← twoChart_dom_eq (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)]; exact hz
    obtain ⟨hf, hl⟩ := twoChart_fwd_lift_eq (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω) hz'
    change _ = _ - chiC κ * (twoChart _ t₀ _ r).2.2 z
    rw [show (stopChart κ b jumps θ₀ t₀ θ r E ω).1 z = (twoChart _ t₀ _ r).1 z from rfl, hf, hl]
    change _ = _ - chiC κ * ((logDerivFwd _ _ z).im + 0)
    unfold couplingMean
    simp only [add_zero]
    rfl
  -- harmonicity of the stage mean on the domain
  have hmharm : ∀ ω, InnerProductSpace.HarmonicOnNhd (m ω) (D ω) := by
    intro ω
    rw [hD]
    dsimp only
    split_ifs with hω
    · intro z hz
      have hc := continuous_rpath_catPath (T₀ := t₀) (hWc 0 ω) (hWc 1 ω) (hW0 1 ω)
      have hz' := (mem_dom_catChart_iff (T₁ := r) (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)).1
        (by rw [← twoChart_dom_eq (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)]; exact hz)
      have h1 := SideHeight.harmonicOnNhd_couplingMean (κ := κ) hc (t := ((t₀ + r : ℝ≥0) : ℝ)) (NNReal.coe_nonneg _)
        (BoundaryWord.isBoundedHarmonicExtension_mean (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1))
          (isSorted_stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1))).1 z hz'
      rw [hm]
      exact h1.sub (hu₀.1 z hz'.1)
    · intro z hz
      exact hz.elim
  -- the identity of the means at every test function supported in the domain
  have hφ : ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ H \ (H \ D ω) →
      g ω φ = ∫ z, m ω z * φ z := by
    intro φ
    filter_upwards [hmean φ] with ω hω hsupp
    have hDH : D ω ⊆ H := by
      rw [hD]; dsimp only; split_ifs
      · exact (isConformal_twoChart (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)).dom_subset
      · exact empty_subset _
    rw [sdiff_sdiff_cancel_left hDH] at hsupp
    by_cases hωG : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E
    · have hsD : tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom := by
        rw [hD] at hsupp; simp only [hωG, ↓reduceIte] at hsupp; exact hsupp
      rw [hω hωG hsD, hm]
      have hc1 : ContinuousOn (fun z => (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean
          ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z) - chiC κ * (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z)
          (stopChart κ b jumps θ₀ t₀ θ r E ω).dom := by
        have hcon := isConformal_twoChart (T₀ := t₀) (T₁ := r) (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)
        exact ((BoundaryWord.continuousOn_mean _).comp hcon.differentiableOn_fwd.continuousOn
          fun z hz => hcon.fwd_mem hz).sub
          ((continuousOn_lift_twoChart (fun ω => hWc 0 ω) (fun ω => hW0 0 ω) (fun ω => hWc 1 ω)
            (fun ω => hW0 1 ω) ω).const_smul (chiC κ))
      have hi1 := WholeField.integrable_mul_testOn hc1 φ hsD
      have hi2 := WholeField.integrable_mul_testOn (fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt) φ
        φ.tsupport_subset
      rw [← integral_sub hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hzφ : φ z = 0
      · simp only [hzφ, mul_zero, sub_zero]
      · have hz : z ∈ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom := hsD (subset_tsupport _ hzφ)
        simp only
        rw [hcm ω z hz]
        ring
    · rw [hD] at hsupp
      simp only [hωG, ↓reduceIte] at hsupp
      have h0 := Restart.eq_zero_of_tsupport_subset_empty hsupp
      subst h0
      simp
  have hall := WangWu.ae_forall_apply_eq_of_forall_ae (A := fun ω => H \ D ω) (m := m)
    (by
      filter_upwards [hg.2.1, hAD] with ω hgω hADω
      have hDH : D ω ⊆ H := by
        rw [hD]; dsimp only; split_ifs
        · exact (isConformal_twoChart (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)).dom_subset
        · exact empty_subset _
      rw [sdiff_sdiff_cancel_left hDH]
      refine IsHarmonicDistOn.mono hgω ?_
      rw [hD]; dsimp only; split_ifs with hω
      · exact (hADω hω).1
      · exact empty_subset _)
    (Eventually.of_forall fun ω => by
      have hDH : D ω ⊆ H := by
        rw [hD]; dsimp only; split_ifs
        · exact (isConformal_twoChart (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)).dom_subset
        · exact empty_subset _
      rw [sdiff_sdiff_cancel_left hDH, hD]; dsimp only; split_ifs
      · exact (stopChart κ b jumps θ₀ t₀ θ r E ω).dom.isOpen
      · exact isOpen_empty)
    (Eventually.of_forall fun ω => by
      have hDH : D ω ⊆ H := by
        rw [hD]; dsimp only; split_ifs
        · exact (isConformal_twoChart (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)).dom_subset
        · exact empty_subset _
      rw [sdiff_sdiff_cancel_left hDH]
      exact hmharm ω) hφ
  filter_upwards [hall, hAD] with ω hallω hADω hωG v hv hrep W' α ζ hgα hWc' hW0' hagr hinj hTr t₁ hTt ht₁ hH
  obtain ⟨hDA, -⟩ := hADω hωG
  have hDω : D ω = (stopChart κ b jumps θ₀ t₀ θ r E ω).dom := by rw [hD]; simp only [hωG, ↓reduceIte]
  have hDH : D ω ⊆ H := by
    rw [hDω]; exact (isConformal_twoChart (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)).dom_subset
  have hDo : IsOpen (D ω) := by rw [hDω]; exact (stopChart κ b jumps θ₀ t₀ θ r E ω).dom.isOpen
  -- the harmonic representative is the stage mean on the domain
  have heq : EqOn v (m ω) (D ω) := by
    refine Sec6.eqOn_of_integral_mul_eq hDo hDH (fun z hz => hv z (by rw [hDω] at hz; exact hDA hz))
      (hmharm ω) fun φ hφ => ?_
    have h1 := hallω φ (by rw [sdiff_sdiff_cancel_left hDH]; exact hφ)
    rw [← h1, hrep φ (hφ.trans (by rw [hDω]; exact hDA))]
  refine hasSideHeights_of_eqOn_stageMean (hWc 0 ω) (hW0 0 ω) (recsTwo κ b jumps θ₀ t₀ θ r E ω 1) rfl
    (rtime_recsTwo_one hωG) (β ω) θ hgα hWc' hW0' hagr hinj hTr hTt ht₁ hH fun z hz => ?_
  have hzD : z ∈ D ω := by rw [hDω]; exact hz
  have h1 := heq hzD
  rw [hm] at h1
  simp only at h1
  simp only
  rw [h1, hcm ω z hz]
  ring

end Final

end StripSideHeightProb

end Sec7

end InteractingSLE
