/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RqInv
import InteractingSLE.Spec.Sec7.ContinuityProb2Join
import InteractingSLE.Spec.Supplement.SB2McTrace
import InteractingSLE.Spec.Supplement.SB2MbFill
import InteractingSLE.Spec.Supplement.SB2LkDom
import InteractingSLE.Spec.Supplement.Q3ChainMeas
import InteractingSLE.Spec.Supplement.RelTransHull
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfSide
import InteractingSLE.Spec.Sec5.CrossCondGenFinalMarks
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalFlow
import InteractingSLE.Spec.Supplement.LPProbReflect

/-!
# A piece whose trace avoids the angle regions is split-free (decision D33)

PROVE-GW2-ROOTX round 8, the deterministic Loewner step. Take a continuous driver `w` (`w 0 = 0`) with a generating
trace `η` beyond a time `T`. If `η` has no real point in `(0, aR)` up to `T`, then at `T` the right mark flow either
keeps `(0, aR]` alive (and is strictly increasing on `[0, aR]`) or has swallowed all of it (`markPos aR = markPos 0`).
A point is swallowed iff it lies in the closed hull (`Aux10.exists_isForwardSol_of_notMem_closure`,
`Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol`), which is the fill of the trace
(`SB.Lk.fwdHull_eq_fillH_horizon`), read on the real line from real trace points
(`SB.Lk.mem_closure_fillH_image_iff`, `SB.Lk.trace_mem_closure_fillH`).
If the tip at `T > 0` is interior, the seed image is positive (`CrossCond.Gen.chartAR_pos_of_interior_tip` through a
frozen global trace, `CrossRestart.exists_frozen_isLoewnerTrace`).

* **`splitFreeR_of_trace`**; **`splitFreeL_of_trace`** (by reflection, `LP.isGeneratingTrace_reflect`);
* **`splitFree_of_trace`**: the two sides, for the record driver `fun x => w x.toNNReal`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap IsForwardSol)

namespace InteractingSLE.Theorem14.GW2Rq

open Restart Exist.StagedLaw

variable {wN : ℝ≥0 → ℝ} {T : ℝ≥0} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The right side of a piece whose trace avoids `(0, aR)`.** -/
theorem splitFreeR_of_trace (hwc : Continuous wN) (hw0 : wN 0 = 0) (hTζ : (T : ℝ≥0∞) < ζ)
    (hη : IsGeneratingTrace wN ζ η) {aR : ℝ} (haR : 0 ≤ aR)
    (hvis : ∀ t : ℝ≥0, t ≤ T → (η t).im = 0 → (η t).re ∉ Ioo 0 aR) (htip : 0 < T → η T ∈ H) :
    (StrictMonoOn (markPos (fun x : ℝ => wN x.toNNReal) T) (Icc 0 aR) ∧
        (0 < (T : ℝ) → 0 < markPos (fun x : ℝ => wN x.toNNReal) T 0)) ∨
      markPos (fun x : ℝ => wN x.toNNReal) T aR = markPos (fun x : ℝ => wN x.toNNReal) T 0 := by
  classical
  set w : ℝ → ℝ := fun x => wN x.toNNReal with hwdef
  have hw : Continuous w := hwc.comp continuous_real_toNNReal
  have hw0' : w 0 = 0 := by simp only [hwdef, Real.toNNReal_zero, hw0]
  have hT0 : (0 : ℝ) ≤ T := T.coe_nonneg
  have hηT : IsGeneratingTrace wN T η := hη.mono hTζ.le
  have hK : fwdHull w T = fillH (η '' Icc 0 T) := SB.Lk.fwdHull_eq_fillH_horizon hwc hw0 hηT
  have hwcon : ContinuousOn wN {s | (s : ℝ≥0∞) < T} := hwc.continuousOn
  have hHbar : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → η t ∈ Hbar := fun t ht =>
    Sec7.IsGeneratingTrace.mem_Hbar hηT hwcon hw0 ht
  -- the trace frozen after `T`, a continuous curve in `ℍ̄`
  set β' : ℝ≥0 → ℂ := fun t => η (min t T) with hβ'
  have hβc : Continuous β' := by
    have hc : ContinuousOn η (Icc 0 T) := hηT.2.1.mono fun s hs => ENNReal.coe_le_coe.2 hs.2
    refine hc.comp_continuous (continuous_id.min continuous_const) fun t => ⟨zero_le, min_le_right _ _⟩
  have hβH : ∀ t, β' t ∈ Hbar := fun t => hHbar _ (ENNReal.coe_le_coe.2 (min_le_right _ _))
  have hβimg : β' '' Icc 0 T = η '' Icc 0 T := by
    ext z
    simp only [mem_image, mem_Icc, hβ']
    constructor
    · rintro ⟨t, ht, rfl⟩; exact ⟨min t T, ⟨zero_le, min_le_right _ _⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩; exact ⟨t, ht, by rw [min_eq_left ht.2]⟩
  have hβ0 : β' 0 = 0 := by simp only [hβ', min_eq_left (zero_le : (0 : ℝ≥0) ≤ T), hηT.1]
  have hηimH : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ T → 0 ≤ (η t).im := fun t ht => hHbar t ht
  -- aliveness and the closed hull
  have halive_iff : ∀ x : ℝ, 0 < x → ((∃ v, IsForwardSol w (x : ℂ) T v) ↔ (x : ℂ) ∉ closure (fwdHull w T)) :=
    fun x hx => ⟨fun ⟨v, hv⟩ => Supp8.RelTrans.notMem_closure_fwdHull_of_isForwardSol hw hT0 hv,
      fun h => Aux10.exists_isForwardSol_of_notMem_closure hw hw0' hT0 hx.ne' h⟩
  -- a dead point is beaten by a real trace point
  have hdead : ∀ x : ℝ, 0 < x → ¬ (∃ v, IsForwardSol w (x : ℂ) T v) →
      ∃ t : ℝ≥0, t ≤ T ∧ (η t).im = 0 ∧ x ≤ (η t).re := by
    intro x hx hd
    have hcl : (x : ℂ) ∈ closure (fillH (η '' Icc 0 T)) := by
      rw [← hK]; by_contra h; exact hd ((halive_iff x hx).2 h)
    by_cases hxP : (x : ℂ) ∈ η '' Icc 0 T
    · obtain ⟨t, ht, he⟩ := hxP
      exact ⟨t, ht.2, by rw [he]; simp, by rw [he]; simp⟩
    · rw [← hβimg] at hcl hxP
      obtain ⟨t, ht, him, hlt⟩ := (SB.Lk.mem_closure_fillH_image_iff hβc hβH (zero_le : (0 : ℝ≥0) ≤ T) hβ0 hx
        hxP).1 hcl
      refine ⟨t, ht.2, ?_, ?_⟩
      · simpa [hβ', min_eq_left ht.2] using him
      · have := hlt.le; simpa [hβ', min_eq_left ht.2] using this
  -- every point below a real trace point is dead
  have hkill : ∀ t₀ : ℝ≥0, t₀ ≤ T → (η t₀).im = 0 → ∀ x : ℝ, 0 < x → x ≤ (η t₀).re →
      ¬ (∃ v, IsForwardSol w (x : ℂ) T v) := by
    intro t₀ ht₀ him x hx hxy hal
    have hnot := (halive_iff x hx).1 hal
    rw [hK] at hnot
    by_cases hxP : (x : ℂ) ∈ η '' Icc 0 T
    · obtain ⟨t, ht, he⟩ := hxP
      have ht0 : 0 < t := by
        rcases (zero_le : (0 : ℝ≥0) ≤ t).lt_or_eq with h | h
        · exact h
        · rw [← h, hηT.1] at he
          exact absurd (congrArg Complex.re he) (by simp; exact hx.ne)
      exact hnot (he ▸ SB.Lk.trace_mem_closure_fillH hηT hwc hw0 hηimH ht0 ht.2)
    · have hxlt : x < (η t₀).re := by
        rcases hxy.lt_or_eq with h | h
        · exact h
        · exfalso
          apply hxP
          refine ⟨t₀, ⟨zero_le, ht₀⟩, ?_⟩
          exact Complex.ext (by simp [h]) (by simp [him])
      rw [← hβimg] at hnot hxP
      exact hnot ((SB.Lk.mem_closure_fillH_image_iff hβc hβH (zero_le : (0 : ℝ≥0) ≤ T) hβ0 hx hxP).2
        ⟨t₀, ⟨zero_le, ht₀⟩, by simpa [hβ', min_eq_left ht₀] using him,
          by simpa [hβ', min_eq_left ht₀] using hxlt⟩)
  by_cases hall : ∀ x ∈ Ioc 0 aR, ∃ v, IsForwardSol w (x : ℂ) T v
  · left
    refine ⟨fun x hx y hy hxy => ?_, fun hTpos => ?_⟩
    · -- strict monotonicity on alive points
      have hy0 : 0 < y := lt_of_le_of_lt hx.1 hxy
      set z := max x (y / 2) with hz
      have hz0 : 0 < z := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hzy : z < y := max_lt hxy (by linarith)
      have hzal := hall z ⟨hz0, hzy.le.trans hy.2⟩
      have h1 : markPos w T x ≤ markPos w T z := GW1W.markPos_mono hw hw0' hT0 hx.1 (le_max_left _ _)
      have h2 : markPos w T z = (fwdMap w T z).re := GW2Wm.markPos_eq_re_fwdMap hw hw0' hT0 hz0 hzal
      by_contra hle
      push Not at hle
      have := (GW1W.markPos_le_iff hw hw0' hT0 hy0.le hz0 hzal).1 (by linarith)
      linarith
    · -- the seed image is positive at an interior tip
      have hTpos' : 0 < T := by exact_mod_cast hTpos
      obtain ⟨V, α, hV, hV0, hVα, hVw, hαη, -⟩ :=
        Sec5.CrossRestart.exists_frozen_isLoewnerTrace hη hwc.continuousOn hw0 hTζ
      have htipα : α T ∈ H := by
        rw [hαη T ⟨hT0, le_rfl⟩]
        simpa using htip hTpos'
      have hpos := Sec5.CrossCond.Gen.chartAR_pos_of_interior_tip hVα htipα hV hV0 hTpos
      have heq : WangWu.chartAR V T = WangWu.chartAR w T :=
        Supp8.Q3Chain.chartAR_eq_of_eqOn hw hT0 fun r hr => hVw r hr
      rw [Sec5.CrossCond.StagedFinal.markPos_zero_eq_chartAR hw hw0' hT0, ← heq]
      exact hpos
  · right
    push Not at hall
    obtain ⟨x, hx, hxd⟩ := hall
    obtain ⟨t₀, ht₀, him, hxle⟩ := hdead x hx.1 (fun ⟨v, hv⟩ => hxd v hv)
    have hyR : aR ≤ (η t₀).re := by
      by_contra hlt
      push Not at hlt
      exact hvis t₀ ht₀ him ⟨hx.1.trans_le hxle, hlt⟩
    -- every rational of `(0, aR]` is dead, so the two infima agree
    unfold markPos
    congr 1
    refine iInf_congr fun q => ?_
    unfold markTerm
    by_cases hq : (0 : ℝ) < q
    · by_cases hqa : (q : ℝ) ≤ aR
      · have hqd := hkill t₀ ht₀ him q hq (hqa.trans hyR)
        rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hqd h.2),
          ite_eq_right_of_eq_false _ _ (eq_false fun h => hqd h.2)]
      · push Not at hqa
        have e : (aR < (q : ℝ) ∧ ∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u) ↔
            ((0 : ℝ) < q ∧ ∃ u, IsForwardSol w ((q : ℝ) : ℂ) T u) :=
          ⟨fun h => ⟨hq, h.2⟩, fun h => ⟨hqa, h.2⟩⟩
        simp only [e]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false fun h => hq (haR.trans_lt h.1)),
        ite_eq_right_of_eq_false _ _ (eq_false fun h => hq h.1)]

/-- **The left side of a piece whose trace avoids `(aL, 0)`** (the right side for the reflected driver). -/
theorem splitFreeL_of_trace (hwc : Continuous wN) (hw0 : wN 0 = 0) (hTζ : (T : ℝ≥0∞) < ζ)
    (hη : IsGeneratingTrace wN ζ η) {aL : ℝ} (haL : aL ≤ 0)
    (hvis : ∀ t : ℝ≥0, t ≤ T → (η t).im = 0 → (η t).re ∉ Ioo aL 0) (htip : 0 < T → η T ∈ H) :
    (StrictMonoOn (markPosL (fun x : ℝ => wN x.toNNReal) T) (Icc aL 0) ∧
        (0 < (T : ℝ) → markPosL (fun x : ℝ => wN x.toNNReal) T 0 < 0)) ∨
      markPosL (fun x : ℝ => wN x.toNNReal) T aL = markPosL (fun x : ℝ => wN x.toNNReal) T 0 := by
  have hR := splitFreeR_of_trace (wN := -wN) (η := fun t => LP.reflectC (η t)) hwc.neg (by simp [hw0]) hTζ
    (LP.isGeneratingTrace_reflect hη) (aR := -aL) (by linarith) (fun t ht him hre => by
      have him' : (η t).im = 0 := by simpa [LP.reflectC] using him
      apply hvis t ht him'
      have : (LP.reflectC (η t)).re = -(η t).re := by simp [LP.reflectC]
      rw [this] at hre
      exact ⟨by linarith [hre.2], by linarith [hre.1]⟩)
    (fun hT => by
      have := htip hT
      simpa [LP.reflectC, QuantumZipper.H] using this)
  have e : ∀ x : ℝ, markPosL (fun x : ℝ => wN x.toNNReal) T x = -markPos (fun x : ℝ => (-wN) x.toNNReal) T (-x) :=
    fun x => rfl
  rcases hR with ⟨hA, hseed⟩ | hB
  · left
    refine ⟨fun x hx y hy hxy => ?_, fun hT => ?_⟩
    · rw [e, e]
      have := hA ⟨by linarith [hy.2], by linarith [hy.1]⟩ ⟨by linarith [hx.2], by linarith [hx.1]⟩
        (show -y < -x by linarith)
      linarith
    · rw [e, neg_zero]
      linarith [hseed hT]
  · right
    rw [e, e, neg_zero, hB]

/-- **A piece whose trace avoids both angle regions up to `T`, with an interior tip at `T`, is split-free.** -/
theorem splitFree_of_trace {r : RecData} {wN : ℝ≥0 → ℝ} (hwc : Continuous wN) (hw0 : wN 0 = 0)
    (hrd : rdrv r = fun x : ℝ => wN x.toNNReal) {T : ℝ≥0} (hrt : rtime r = T) {ζ : ℝ≥0∞} (hTζ : (T : ℝ≥0∞) < ζ)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace wN ζ η) {aL aR : ℝ} (haL : aL ≤ 0) (haR : 0 ≤ aR)
    (hvis : ∀ t : ℝ≥0, t ≤ T → (η t).im = 0 → (η t).re ∉ Ioo aL 0 ∧ (η t).re ∉ Ioo 0 aR)
    (htip : 0 < T → η T ∈ H) : SplitFree r aL aR := by
  unfold SplitFree
  rw [hrd, hrt]
  exact ⟨splitFreeR_of_trace hwc hw0 hTζ hη haR (fun t ht him => (hvis t ht him).2) htip,
    splitFreeL_of_trace hwc hw0 hTζ hη haL (fun t ht him => (hvis t ht him).1) htip⟩

end InteractingSLE.Theorem14.GW2Rq
